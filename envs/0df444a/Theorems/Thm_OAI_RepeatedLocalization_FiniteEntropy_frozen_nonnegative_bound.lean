-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_frozen_nonnegative_bound
-- name    : OAI.RepeatedLocalization.FiniteEntropy.frozen_nonnegative_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T20:03:26.476813+00:00
-- url     : https://prove2.me/theorems/5f8d9867-3a38-4dc6-8fca-078715893423
-- title:
--   Integral bound for the limit of an almost surely eventually constant sequence of nonnegative functions
-- statement:
--   Let $(\alpha,\mathcal A)$ be a measurable space with a measure $P$ (not assumed to be finite), let $f_N:\alpha\to\mathbb R$ for $N\in\mathbb N$, let $F:\alpha\to\mathbb R$, and let $B\ge0$. Assume that:
--
--   1. every $f_N$ is $P$-integrable, and $f_N(z)\ge0$ for all $N$ and all $z$;
--   2. $F$ is almost everywhere strongly measurable, and $F(z)\ge0$ for all $z$;
--   3. the sequence freezes at $F$ almost surely: for $P$-almost every $z$ there is $N_z$ such that $f_M(z)=F(z)$ for all $M\ge N_z$;
--   4. $\int f_N\,dP\le B$ for every $N$.
--
--   Then $F$ is $P$-integrable and
--
--   $$
--   \int_\alpha F\,dP\;\le\;B .
--   $$
--
--   This is a version of Fatou's lemma tailored to quantities computed from truncated runs of a procedure that stops almost surely: once a run has stopped, the truncated quantity no longer changes and equals its terminal value. It transfers bounds that hold uniformly in the truncation level (for the conditional divergence plus depth, and for the number of attempts) to the terminal quantities, including their integrability.
--
--   **Formalization Note** Almost-everywhere strong measurability is `AEStronglyMeasurable F P`; for real-valued functions it amounts to agreeing almost everywhere with a measurable function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/Termination.lean#L34-L60

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards
import Definitions.Def_OAI_Probability_Localization_RewardBounds
import Definitions.Def_OAI_Probability_Localization_EntropyBudget

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Filter
open scoped Topology

theorem OAI.RepeatedLocalization.FiniteEntropy.frozen_nonnegative_bound {α : Type*} [MeasurableSpace α] (P : Measure α)
    (f : ℕ → α → ℝ) (F : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ N,Integrable (f N) P) (hf0 : ∀ N z,0 ≤ f N z)
    (hF : AEStronglyMeasurable F P) (hF0 : ∀ z,0 ≤ F z)
    (hfreeze : ∀ᵐ z ∂P,∃ N,∀ M,N ≤ M → f M z = F z)
    (hbound : ∀ N,(∫ z,f N z ∂P) ≤ B) :
    Integrable F P ∧ (∫ z,F z ∂P) ≤ B := by sorry
