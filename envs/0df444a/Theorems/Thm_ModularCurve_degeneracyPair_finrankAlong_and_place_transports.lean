-- Prove2me | Theorems.Thm_ModularCurve_degeneracyPair_finrankAlong_and_place_transports
-- name    : ModularCurve.degeneracyPair_finrankAlong_and_place_transports
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/25566f06-2ec7-5165-942a-056eccb704cd
-- title:
--   Degeneracy pair at level Ms: degree s+1 and place transport
-- statement:
--   Fix natural numbers $M, s, q'$ with $M, s \neq 0$, $s$ prime, $q'$ prime, $s \neq q'$, and neither $q'$ nor $s$ dividing $M$, and let $k$ be an algebraically closed field of characteristic $q'$. Write $F_N$ for `modularFunctionFieldC k N`, the intermediate field of the Laurent series field `LaurentSeries k` obtained by adjoining over $k$ the two series `jqModC k` and `jqNModC k N`. Let $\varphi_0, \varphi_1 : F_M \to F_{Ms}$ be $k$-algebra maps (indexed by `Fin 2`) whose underlying ring maps are integral, such that $\varphi_0$ is the identity on Laurent series (so it is the inclusion of subfields) and $\varphi_1$ acts as `qExpand k s`, the endomorphism of `LaurentSeries k` multiplying all exponents by $s$. Then five assertions hold. First, for each $i$, $F_{Ms}$ regarded as an $F_M$-module via $\varphi_i$ has finite rank $s+1$. Second, for each $i$ and each place $p$ of $F_{Ms}$ over $k$ (a valuation subring containing the image of $k$, proper, and a principal ideal ring), the restriction of $p$ along $\varphi_i$ — the preimage valuation subring — is rational, i.e. $k$ surjects onto its residue field, if and only if $p$ is. Third, with the same quantifiers, the restriction along $\varphi_i$ is an affine geometric place, meaning both `jGeomGen k M` and `jNGeomGen k M` lie in its valuation subring, if and only if $p$ is affine in the same sense at level $Ms$. Fourth, for an affine geometric place $p$, the residual value of `jGeomGen k M` at the restriction of $p$ along $\varphi_0$ equals that of `jGeomGen k (M * s)` at $p$, where residual values are taken in $k$ via the inverse of $k \to$ residue field. Fifth, for an affine geometric place $p$ and any `ModularPolynomialData s`, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree `dedekindPsi s` satisfying $\Phi(j, j(q^s)) = 0$ on $q$-expansions, the residual value of `jGeomGen k M` at the restriction of $p$ along $\varphi_1$ is a root of $\Phi$ reduced into $k$ and specialised in its inner variable at the residual value of `jGeomGen k (M * s)` at $p$.
--
--   This is the characteristic-$q'$ form of the basic properties of the two degeneracy maps $X_0(Ms) \rightrightarrows X_0(M)$ for a prime $s$ not dividing $Mq'$: both have degree $s+1 = \psi(s)$, both preserve and reflect rationality and affineness of places, and on $j$-invariants one map is the identity while the other is governed by the modular equation $\Phi_s$. It feeds the analysis of the level-$s$ Hecke correspondence in characteristic $q'$, in particular the stability of supersingular places and the ramification computations for the two degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degeneracyPair_finrankAlong_and_place_transports.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_FibrePoly

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve ModularCurve

theorem ModularCurve.degeneracyPair_finrankAlong_and_place_transports
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
        = qExpand k s x),
    (∀ i, finrankAlong k (φ i) = s + 1) ∧
    (∀ (i : Fin 2) (p : Place k ↥(modularFunctionFieldC k (M * s))),
      (Place.restrictAlong (φ i) (hφ i) p).IsRational ↔ p.IsRational) ∧
    (∀ (i : Fin 2) (p : Place k ↥(modularFunctionFieldC k (M * s))),
      IsAffineGeomPlace k M (Place.restrictAlong (φ i) (hφ i) p) ↔ IsAffineGeomPlace k (M * s) p) ∧
    (∀ (p : Place k ↥(modularFunctionFieldC k (M * s))), IsAffineGeomPlace k (M * s) p →
      (Place.restrictAlong (φ 0) (hφ 0) p).evalAt (jGeomGen k M) = p.evalAt (jGeomGen k (M * s))) ∧
    (∀ (p : Place k ↥(modularFunctionFieldC k (M * s))), IsAffineGeomPlace k (M * s) p →
      ∀ data : ModularPolynomialData s,
        (fibrePoly data.Φ (p.evalAt (jGeomGen k (M * s)))).IsRoot
          ((Place.restrictAlong (φ 1) (hφ 1) p).evalAt (jGeomGen k M))) := by sorry
