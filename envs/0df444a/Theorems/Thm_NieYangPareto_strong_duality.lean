-- Prove2me | Theorems.Thm_NieYangPareto_strong_duality
-- name    : NieYangPareto.strong_duality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:42.692979+00:00
-- url     : https://prove2.me/theorems/bf68cae3-5e6d-407f-915e-e2de021c5ee0
-- title:
--   Proof of Theorem 3.2 — strong duality between (3.2) and (3.3)
-- statement:
--   Let $m\ge1$, let $K$ have nonempty interior and let $v\in\mathbb R^m$. Then the programs (3.2) and (3.3) have the same optimal value:
--
--   $$
--   \omega^*(v)=t^*(v)
--   $$
--
--   as extended reals. This covers the case in which (3.2) is infeasible and (3.3) is unbounded below.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - encoding: tms y ∈ ℝ^{ℕⁿ_d} → y : TmsIndex n d → ℝ, on the finite subtype {α : Fin n →₀ ℕ // α.degree ≤ d}, with the product topology; reason: the same finite-dimensional Euclidean space
--   - encoding: y = ∫[x]_d dμ in (2.2) → each monomial of degree ≤ d is μ-integrable and y_α = ∫x^α dμ; reason: this is what the page's equation means; it stops the junk value ∫ = 0 from entering
--   - reading: (3.2), (3.3) introduced "for given v ∈ f(K)" (p.8) → v ranges over all of ℝ^m; reason: the proof of Theorem 3.2 (p.9) applies them to arbitrary v
--   - reading: "max" in (3.2) → supremum in EReal, so that ω* = ⊥ exactly when (3.2) is infeasible; reason: the page compares optimal values and speaks of infeasibility; a real supremum would return the junk value 0
--   - reading: "min" in (3.3) → infimum in EReal, with no attainment claim; reason: the page compares optimal values; a real infimum would return the junk value 0
--   - reading: m unbounded below ("several objective functions") → hypothesis 0 < m; reason: at m = 0 the equality of (3.3) reads 1 = 0 and eᵀw = 1 reads 0 = 1, so the programs are meaningless there
--   - reading: "the strong duality holds between (3.2) and (3.3)" → ω* = t* in EReal; reason: the proof uses it only to compare the optimal values; the zero-gap meaning of the phrase, the standard one
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, proof of Theorem 3.2, p.9

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_Programs

namespace NieYangPareto

/-- **Strong duality between (3.2) and (3.3).** Nie–Yang, arXiv:2108.04336v2, proof of Theorem 3.2,
p.9: "Hence, the strong duality holds between (3.2) and (3.3), since (3.3) has strictly feasible
points."

**Formalization Note** The two optimal values are equal in `EReal`, which covers both the finite case
and "(3.2) infeasible, (3.3) unbounded". `v` is arbitrary, as in the page's proof. `0 < m` is needed:
for `m = 0` the equality of (3.3) reads `1 = 0`. -/
theorem strong_duality {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (hK : (interior P.K).Nonempty) (hm : 0 < m) (v : Fin m → ℝ) :
    P.omegaStar v = P.tStar v := by sorry

end NieYangPareto
