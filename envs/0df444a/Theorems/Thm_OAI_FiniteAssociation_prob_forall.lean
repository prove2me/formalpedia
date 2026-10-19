-- Prove2me | Theorems.Thm_OAI_FiniteAssociation_prob_forall
-- name    : OAI.FiniteAssociation.prob_forall
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:46:13.293987+00:00
-- url     : https://prove2.me/theorems/2b77fb29-ce87-4671-a991-c0a24d416ccc
-- title:
--   Harris inequality for finitely many decreasing events
-- statement:
--   For a finite index set $E$ and parameters $p_e\in[0,1]$, $\mathbb P_p$ is the product law of independent bits with $\mathbb P(\omega_e=1)=p_e$, and $\mathbb E_p$ its expectation; configurations are ordered coordinatewise. For finitely many decreasing events $A_i$ (closed under turning bits off), $i\in s$,
--   $$
--   \prod_{i\in s}\mathbb P_p(A_i)\le\mathbb P_p\Bigl(\bigcap_{i\in s}A_i\Bigr).
--   $$
--
--   Decreasing events are positively correlated.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ProductCylinder.lean#L231-L245

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder

open OAI OAI.FiniteAssociation
universe uE uF uI
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
universe u
variable {E : Type u}

theorem OAI.FiniteAssociation.prob_forall [Fintype E] {I : Type uI} (p : E → Set.Icc (0 : ℝ) 1)
    (s : Finset I) (P : I → (E → Bool) → Prop) (hP : ∀ i ∈ s, Antitone (P i)) :
    (∏ i ∈ s, prob p (P i)) ≤ prob p (fun ω => ∀ i ∈ s, P i ω) := by sorry
