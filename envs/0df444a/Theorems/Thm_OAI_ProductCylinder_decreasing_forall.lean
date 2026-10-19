-- Prove2me | Theorems.Thm_OAI_ProductCylinder_decreasing_forall
-- name    : OAI.ProductCylinder.decreasing_forall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:46:44.334699+00:00
-- url     : https://prove2.me/theorems/68c02171-1067-422b-9d2c-19902b9c6158
-- title:
--   Harris inequality for decreasing cylinder events of the infinite product
-- statement:
--   Let $\mathbb P_p$ be the product Bernoulli law on $\{0,1\}^E$ with parameters $p_e$, and let $A_i$, $i$ in a finite set, be decreasing events determined by the bits in a finite set $J$. Then
--   $$
--   \prod_i\mathbb P_p(A_i)\le\mathbb P_p\Bigl(\bigcap_iA_i\Bigr).
--   $$
--
--   Only finitely many bits matter, so the finite Harris inequality applies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ProductCylinder.lean#L259-L284

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

theorem OAI.ProductCylinder.decreasing_forall {I : Type uI} [Fintype I] (J : Finset E)
    (p : E → Set.Icc (0 : ℝ) 1) (A : I → Set (E → Bool))
    (hA : ∀ i ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A i ↔ ω ∈ A i))
    (hmono : ∀ i, Antitone (fun ω => ω ∈ A i)) :
    (∏ i, (law p).real (A i)) ≤ (law p).real (⋂ i, A i) := by sorry
