-- Prove2me | Theorems.Thm_ModularCurve_degeneracyPair_finite_separable_identity_ssPlaces
-- name    : ModularCurve.degeneracyPair_finite_separable_identity_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/37faada4-48eb-5632-92ea-6e4c0bdcbd05
-- title:
--   Degeneracy pair at level Ms: finiteness, separability, supersingular places
-- statement:
--   Let $M,s,q'$ be natural numbers with $M\neq 0$, $s\neq 0$, $s$ prime, $q'$ prime (as a `Fact`), $s\neq q'$, $q'\nmid M$ and $s\nmid M$, and let $k$ be an algebraically closed field of characteristic $q'$ with decidable equality; the product $M\cdot s$ is then nonzero. For $N\neq 0$ write $F_N=$ `modularFunctionFieldC k N`, the intermediate field of the Laurent series field $k((q))$ generated over $k$ by the $q$-expansion `jqModC k` of $j$ and its substitution `jqNModC k N` $=$ `qExpand k N` applied to it. The assertion is: for every pair $\varphi:\mathrm{Fin}\,2\to (F_M\to_{\mathrm{alg}[k]}F_{Ms})$ of $k$-algebra homomorphisms such that each $\varphi_i$ is integral as a ring homomorphism, such that $\varphi_0$ is the identity on underlying Laurent series, and such that $\varphi_1$ acts on Laurent series as the operator `qExpand k s` ($q\mapsto q^{s}$), one has: (i) each $\varphi_i$ is finite, i.e. $F_{Ms}$ is a finite module over $F_M$ via $\varphi_i$; (ii) each $\varphi_i$ is separable for that algebra structure; (iii) for every place $p$ of $F_{Ms}$ over $k$ (a proper valuation subring containing $k$ and a principal ideal ring) lying in `ssPlaces q' (M*s) k`, the restriction of $p$ along $\varphi_0$ lies in `ssPlaces q' M k`; and (iv) conversely, if $v\in$ `ssPlaces q' M k` and $p$ is a place of $F_{Ms}$ restricting along $\varphi_0$ to $v$, then $p\in$ `ssPlaces q' (M*s) k`. Here membership in `ssPlaces q' N k` means that the place is rational, is an affine geometric place for level $N$, and its value at the generator `jGeomGen k N` lies in the set `ssJSet q' k` of supersingular values in characteristic $q'$.
--
--   This is the characteristic-$q'$ form of the standard degeneracy pair $X_0(Ms)\rightrightarrows X_0(M)$ for $s$ prime, $s\nmid M$ and $q'\nmid Ms$: both legs of the pair are finite separable morphisms of function fields, and the supersingular locus is both preserved and reflected along the identity leg. It feeds the combined statement [`ModularCurve.degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected`](thm.html#ModularCurve.degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected), which also records the degree of the pair and the transport along the $q\mapsto q^{s}$ leg.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degeneracyPair_finite_separable_identity_ssPlaces.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve
open ModularCurve

theorem ModularCurve.degeneracyPair_finite_separable_identity_ssPlaces
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k)
        = qExpand k s x),
    (∀ i, FiniteAlong k (φ i)) ∧
    (∀ i, SeparableAlong k (φ i)) ∧
    (∀ (p : Place k ↥(modularFunctionFieldC k (M * s))),
      p ∈ ssPlaces q' (M * s) k →
        Place.restrictAlong (φ 0) (hφ 0) p ∈ ssPlaces q' M k) ∧
    (∀ (v : Place k ↥(modularFunctionFieldC k M)),
      v ∈ ssPlaces q' M k →
        ∀ p : Place k ↥(modularFunctionFieldC k (M * s)),
          Place.restrictAlong (φ 0) (hφ 0) p = v → p ∈ ssPlaces q' (M * s) k) := by sorry
