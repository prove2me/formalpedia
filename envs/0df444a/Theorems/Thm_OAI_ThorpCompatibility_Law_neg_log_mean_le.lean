-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_neg_log_mean_le
-- name    : OAI.ThorpCompatibility.Law.neg_log_mean_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:46:19.161412+00:00
-- url     : https://prove2.me/theorems/dadf6366-6ac5-4855-b818-d78f9addf59b
-- title:
--   Jensen's inequality for $-\log$ under a finite probability law
-- statement:
--   Let $\Omega$ be a finite set, $P$ a probability distribution on $\Omega$, and $f:\Omega\to\mathbb{R}$ a function that is positive on the support of $P$ (that is, $f(x)>0$ whenever $P(x)>0$) and has positive mean $\mathbb E_P[f]=\sum_xP(x)f(x)>0$. Then
--
--   $$
--   -\log\mathbb E_P[f]\;\le\;\mathbb E_P[-\log f]=-\sum_{x\in\Omega}P(x)\log f(x).
--   $$
--
--   This is Jensen's inequality for the convex function $-\log$; equivalently, the expected logarithm is at most the logarithm of the expectation. It bounds an expected surprisal $\mathbb E_P[-\log f]$ from below by the surprisal of the averaged quantity $\mathbb E_P[f]$.
--
--   **Formalization Note** The values of $f$ off the support of $P$ are irrelevant, as they are multiplied by $P(x)=0$. The positivity of the mean is stated as a separate hypothesis, although it already follows from the positivity of $f$ on the support.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/EntropyBounds.lean#L58-L77

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem OAI.ThorpCompatibility.Law.neg_log_mean_le (P : Law α) (f : α → ℝ)
    (hf : ∀ a, 0 < P.mass a → 0 < f a) (hmean : 0 < P.mean f) :
    -Real.log (P.mean f) ≤ P.mean (fun a => -Real.log (f a)) := by sorry
