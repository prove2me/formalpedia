-- Prove2me | Theorems.Thm_OAI_ProductCylinder_continuous_probability
-- name    : OAI.ProductCylinder.continuous_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:47:20.232393+00:00
-- url     : https://prove2.me/theorems/368f4f68-5e23-41c5-8323-511a7cb0b142
-- title:
--   Cylinder probabilities depend continuously on the parameters
-- statement:
--   Let $A\subseteq\{0,1\}^E$ be an event determined by the bits in a finite set $J$. Then its probability under the product Bernoulli law is a continuous function of the parameter field:
--   $$
--   p\mapsto\mathbb P_p(A)\ \text{is continuous on }[0,1]^E .
--   $$
--
--   This is what allows lowering a parameter slightly while keeping strict inequalities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ProductCylinder.lean#L296-L318

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder

open OAI OAI.ProductCylinder
universe uE uF uI
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
variable {E : Type uE}

theorem OAI.ProductCylinder.continuous_probability (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    Continuous (fun p : E → Set.Icc (0 : ℝ) 1 => (law p).real A) := by sorry
