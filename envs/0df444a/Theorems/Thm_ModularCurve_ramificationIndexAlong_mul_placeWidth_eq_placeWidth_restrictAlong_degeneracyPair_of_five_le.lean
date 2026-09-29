-- Prove2me | Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le
-- name    : ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/d711c979-b16a-53e8-b23c-373f585b4f69
-- title:
--   Width transport along the degeneracy pair, characteristic ≥ 5
-- statement:
--   Fix natural numbers $M, s, q'$ with $M, s$ nonzero, $s$ prime, $q'$ prime, $5 \le q'$, $s \ne q'$ and $q' \nmid M$, and let $k$ be an algebraically closed field of characteristic $q'$ (in universe `Type`); then $Ms \ne 0$, and the sets $\mathrm{ssPlaces}\,q'\,(Ms)\,k$ and $\mathrm{ssPlaces}\,q'\,M\,k$ of places $w$ of the function field $\mathrm{modularFunctionFieldC}\,k\,N = k(j_q, j_{q,N}) \subseteq \mathrm{LaurentSeries}\,k$ satisfying `IsSupersingularPlace` are taken to be finite. Given maps $ab_i : \mathrm{ssPlaces}\,q'\,(Ms)\,k \to \mathrm{ssPlaces}\,q'\,M\,k$ and $m_i : \mathrm{ssPlaces}\,q'\,(Ms)\,k \to \mathbb{N}$ for $i \in \{0,1\}$, and $k$-algebra homomorphisms $\varphi_i : \mathrm{modularFunctionFieldC}\,k\,M \to \mathrm{modularFunctionFieldC}\,k\,(Ms)$ whose underlying ring maps are integral, such that $\varphi_0$ is the identity on underlying Laurent series and $\varphi_1$ acts as `qExpand k s` (re-indexing the Laurent exponents by multiplication by $s$), and such that $ab_i(p)$ is the place $\mathrm{Place.restrictAlong}\,\varphi_i$ of $p$ and $m_i(p)$ is the ramification index of $p$ along $\varphi_i$, i.e. the least $n > 0$ with $\mathrm{ord}_p(\varphi_i f) = n$ for some nonzero $f$: then for each $i$ and each supersingular place $p$ of level $Ms$ such that $r_{Ms}(p) := \mathrm{ord}_p\bigl(j_q - j_q(p)\bigr)$ divides $W(j_q(p))$, where $W(j) = 3, 2, 1$ according as $j = 0$, $j = 1728$ or otherwise, one has $m_i(p) \cdot \bigl(W(j_q(p))/r_{Ms}(p)\bigr) = W(j_q(ab_i(p)))/r_M(ab_i(p))$, the quotients being natural-number division.
--
--   This is the transport of the automorphism width $W(j)/r(w)$ along the two degeneracy maps relating levels $M$ and $Ms$, in the tame situation where the residue characteristic $q'$ is at least $5$; the width is the local invariant attached to a supersingular place in the character-group computations for $X_0(Ms)$. It feeds the comparison of the two degeneracy legs on supersingular places, in particular the existence statement for the pair of ramification indices along the Hecke maps, the stability of supersingularity under the two restrictions, and the lower bound for orders along the second leg.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve
open ModularCurve

theorem ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_degeneracyPair_of_five_le
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime] (hq5 : 5 ≤ q')
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    {k : Type} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ [Fintype ↥(ssPlaces q' (M * s) k)] [Fintype ↥(ssPlaces q' M k)]
      [DecidableEq ↥(ssPlaces q' (M * s) k)] [DecidableEq ↥(ssPlaces q' M k)],
    ∀ (ab : Fin 2 → ↥(ssPlaces q' (M * s) k) → ↥(ssPlaces q' M k))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) k) → ℕ)
      (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
      (hab : ∀ i p, (ab i p : Place k (modularFunctionFieldC k M))
        = Place.restrictAlong (φ i) (hφ i) ↑p)
      (hm : ∀ i p, m i p = Place.ramificationIndexAlong (φ i)
        (p : Place k (modularFunctionFieldC k (M * s)))),
    ∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) k)),
      placeRamificationJ (M * s) (p : Place k (modularFunctionFieldC k (M * s)))
          ∣ jWidth ((p : Place k (modularFunctionFieldC k (M * s))).evalAt (jGeomGen k (M * s))) →
      m i p * placeWidth (M * s)
          (p : Place k (modularFunctionFieldC k (M * s)))
        = placeWidth M (ab i p : Place k (modularFunctionFieldC k M)) := by sorry
