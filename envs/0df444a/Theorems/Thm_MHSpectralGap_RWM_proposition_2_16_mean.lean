-- Prove2me | Theorems.Thm_MHSpectralGap_RWM_proposition_2_16_mean
-- name    : MHSpectralGap.RWM.proposition_2_16_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:14:08.132198+00:00
-- url     : https://prove2.me/theorems/a403b79f-d55b-40a6-9935-072c99c38e04
-- title:
--   Proposition 2.16, (2.8) second branch, p. 15 — 1 − β ≤ 2C ≤ 2E_µα(x) for a Metropolis–Hastings kernel with atomless target
-- statement:
--   Let $Q$ be a Markov kernel on a measurable space $X$, $\alpha:X\times X\to[0,1]$ jointly measurable, and $P$ the Metropolis–Hastings kernel (1.3) with proposal $Q$ and acceptance probability $\alpha$. Let $\mu$ be an atomless probability measure (every measurable set of positive measure contains a measurable subset of strictly smaller positive measure) for which $P$ is reversible. With $\beta=\|P\|_{L^2_0\to L^2_0}$, $\mathsf C$ the conductance and $\alpha(x)=\int\alpha(x,y)Q(x,dy)$,
--
--   $$
--   1-\beta\;\le\;2\mathsf C\;\le\;2\,\mathbb E_\mu\,\alpha(x)=2\int_X\alpha(x)\,\mu(dx).
--   $$
--
--   The spectral gap is thus controlled by the average acceptance probability under the target, the quantity studied in scaling analyses of Metropolis algorithms.
--
--   **Formalization Note** The atomlessness of $\mu$ is an added hypothesis. Proposition 2.16 asserts $2\mathsf C\le2\mathbb E_\mu\alpha(x)$, while the text just above it on p. 15 derives only $\mathsf C\le 2\mathbb E_\mu\alpha(x)$; the proposition's (stronger) form is stated here, under atomlessness of $\mu$, which holds for the Gaussian targets of the paper. The undefined middle term $1-\Lambda$ of (2.8) is dropped, as in the companion item. Inequalities are in $[0,\infty]$.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 15, Proposition 2.16, display (2.8) (second branch)

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel
import Definitions.Def_MHSpectralGap_RWM_L2Gap
import Definitions.Def_MHSpectralGap_RWM_Conductance

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- Proposition 2.16, p. 15, (2.8) second branch: for a Metropolis–Hastings kernel
`P = mhKernel Q α` reversible for an atomless target `μ`, `1 − β ≤ 2C ≤ 2 E_μ α(x)`.
(The atomlessness hypothesis `hatomless` is an addition, see the description.) -/
theorem proposition_2_16_mean {X : Type*} [MeasurableSpace X] (Q : ProbabilityTheory.Kernel X X)
    [ProbabilityTheory.IsMarkovKernel Q] (α : X → X → ℝ≥0∞)
    (hα : Measurable (Function.uncurry α)) (hα1 : ∀ x y, α x y ≤ 1)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hatomless : ∀ A : Set X, MeasurableSet A → 0 < μ A →
      ∃ B ⊆ A, MeasurableSet B ∧ 0 < μ B ∧ μ B < μ A)
    (hrev : (mhKernel Q α).IsReversible μ) :
    ENNReal.ofReal (1 - l2Beta (mhKernel Q α) μ) ≤ 2 * conductance (mhKernel Q α) μ ∧
      2 * conductance (mhKernel Q α) μ ≤ 2 * ∫⁻ x, accBar Q α x ∂μ := by sorry

end MHSpectralGap.RWM
