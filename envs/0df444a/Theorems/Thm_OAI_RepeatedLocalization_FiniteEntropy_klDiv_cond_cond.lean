-- Prove2me | Theorems.Thm_OAI_RepeatedLocalization_FiniteEntropy_klDiv_cond_cond
-- name    : OAI.RepeatedLocalization.FiniteEntropy.klDiv_cond_cond
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:55:40.50727+00:00
-- url     : https://prove2.me/theorems/69e41166-8f3c-42fd-854f-d80f13b588c2
-- title:
--   Relative entropy between conditioned probability measures via the log-likelihood ratio
-- statement:
--   Let $(\alpha,\mathcal A)$ be a measurable space and let $P$ and $\nu$ be probability measures on it with $P\ll\nu$ and finite Kullback–Leibler divergence $\mathrm{KL}(P\,\|\,\nu)<\infty$; write $\log\frac{dP}{d\nu}$ for the log-likelihood ratio. Let $E\subseteq R$ be measurable sets with $P(E)\neq0$ and $\nu(R)\neq0$, and let $P_E=P(\cdot\mid E)$ and $\nu_R=\nu(\cdot\mid R)$ be the conditioned probability measures. Then:
--
--   1. $\mathrm{KL}(P_E\,\|\,\nu_R)<\infty$, and
--   2. the divergence of the conditioned laws is given by the identity below.
--
--   $$
--   P(E)\,\mathrm{KL}(P_E\,\|\,\nu_R)=\int_E\log\frac{dP}{d\nu}\,dP\;-\;P(E)\log P(E)\;+\;P(E)\log\nu(R).
--   $$
--
--   This is the chain rule for relative entropy under conditioning: restricting $P$ to an event $E$ and $\nu$ to a larger region $R$ shifts the log-likelihood ratio by the constant $-\log P(E)+\log\nu(R)$. In the localization argument $\nu$ is the uniform law on a dyadic cell, $E$ is the event of a history and $R$ is the current cell, so that $\nu_R$ is again a uniform law and $\log\nu(R)$ is an explicit multiple of the depth.
--
--   **Formalization Note** The divergence is Mathlib's `InformationTheory.klDiv`, valued in $[0,\infty]$; the identity is stated after converting it, $P(E)$ and $\nu(R)$ to real numbers with `toReal`. The log-likelihood ratio is `llr P ν`, the logarithm of the real-valued Radon–Nikodym derivative (with the convention $\log0=0$), and conditioning is `ProbabilityTheory.cond`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/EntropyChain.lean#L84-L113

import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells
import Definitions.Def_OAI_Probability_Localization_History
import Definitions.Def_OAI_Probability_Localization_Rewards

open OAI OAI.RepeatedLocalization OAI.RepeatedLocalization.FiniteEntropy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

theorem OAI.RepeatedLocalization.FiniteEntropy.klDiv_cond_cond {α : Type*} [MeasurableSpace α] (P ν : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] (hac : P ≪ ν)
    (hK : InformationTheory.klDiv P ν ≠ ∞) {E R : Set α}
    (hE : MeasurableSet E) (hR : MeasurableSet R) (hER : E ⊆ R)
    (hp : P E ≠ 0) (hνR : ν R ≠ 0) :
    InformationTheory.klDiv (ProbabilityTheory.cond P E) (ProbabilityTheory.cond ν R) ≠ ∞ ∧
    (P E).toReal * (InformationTheory.klDiv (ProbabilityTheory.cond P E) (ProbabilityTheory.cond ν R)).toReal =
      (∫ x in E,llr P ν x ∂P) - (P E).toReal * Real.log (P E).toReal +
        (P E).toReal * Real.log (ν R).toReal := by sorry
