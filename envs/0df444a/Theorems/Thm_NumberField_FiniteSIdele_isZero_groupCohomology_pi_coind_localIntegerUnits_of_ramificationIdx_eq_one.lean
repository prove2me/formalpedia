-- Prove2me | Theorems.Thm_NumberField_FiniteSIdele_isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one
-- name    : NumberField.FiniteSIdele.isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/79541864-dd15-5f92-b570-d3c81fdc65ad
-- title:
--   Vanishing of Hⁿ⁺¹ for unramified local integral units
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra which is Galois over $E$, and write $G = K \simeq_{\mathrm{alg}[E]} K$ for its Galois group. Let $V$ be an arbitrary set of height-one primes of $\mathcal{O}_E$, and assume that every height-one prime $w$ of $\mathcal{O}_K$ whose contraction $w \cap \mathcal{O}_E$ lies in $V$ satisfies $e(w \mid w \cap \mathcal{O}_E) = 1$, the ramification index being taken in the sense of `ramificationIdx'`. Let $n$ be a natural number. For each $v \in V$ let $w(v)$ be the chosen prime of $\mathcal{O}_K$ above $v$, let $D_v \le G$ be the decomposition subgroup of the valuation subring attached to $w(v)$, and let $M_v$ be the unit group of the ring of integers of the $w(v)$-adic completion of $K$, regarded as a $\mathbb{Z}$-linear representation of $D_v$ via its multiplicative action. The theorem asserts that the group cohomology of $G$ in degree $n+1$ with coefficients in the product representation $\prod_{v \in V} \operatorname{Coind}_{D_v}^{G} M_v$, the product carrying the coordinatewise $G$-action, is a zero object.
--
--   This is the cohomological triviality in positive degrees of the integral (unramified) part of the idèle group of $K$, for an index set of places of $E$ that may be infinite. It feeds the computation of the cohomology of the unit idèles used in the Herbrand-quotient input to class field theory, being cited by [`M4aHerbrand.isZero_groupCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one`](thm.html#M4aHerbrand.isZero_groupCohomology_unitIdelesTrivialOn_of_ramificationIdx_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_FiniteSIdele_isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_FiniteSIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

theorem NumberField.FiniteSIdele.isZero_groupCohomology_pi_coind_localIntegerUnits_of_ramificationIdx_eq_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (V : Set (HeightOneSpectrum (𝓞 E)))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∈ V → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (n : ℕ) :
    Limits.IsZero (groupCohomology (GroupCohomology.RepPi.obj fun v : V =>
      Rep.coind (NumberField.FiniteSIdele.D E K v.1).subtype (NumberField.FiniteSIdele.localIntegerUnits E K v.1)) (n + 1)) := by sorry
