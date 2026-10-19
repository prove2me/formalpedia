-- Prove2me | Theorems.Thm_OAI_CriticalZ3_zero_one_of_finite_alteration
-- name    : OAI.CriticalZ3.zero_one_of_finite_alteration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:43:45.610077+00:00
-- url     : https://prove2.me/theorems/3dc3cab4-e4e3-41fb-a076-4b9f22140706
-- title:
--   Zero-one law for events insensitive to finite changes
-- statement:
--   Let $\mu$ be a probability law on $\{0,1\}^E$ under which the coordinates $\omega_e$ are independent, and let $A$ be a measurable event such that changing $\omega$ on any finite set of coordinates does not affect membership in $A$. Then
--   $$
--   \mu(A)\in\{0,1\}.
--   $$
--
--   This is Kolmogorov's zero-one law in the form used for the existence of an infinite cluster.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Basic.lean#L386-L427

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

open OAI OAI.CriticalZ3
universe uE uOmega uV
open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology

theorem OAI.CriticalZ3.zero_one_of_finite_alteration {E : Type uE} (μ : Measure (E → Bool))
    (hi : iIndepFun (fun e (ω : E → Bool) => ω e) μ)
    (A : Set (E → Bool)) (hA : MeasurableSet A)
    (hinv : ∀ (J : Finset E) (ω ω' : E → Bool),
      (∀ e ∉ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : μ A = 0 ∨ μ A = 1 := by sorry
