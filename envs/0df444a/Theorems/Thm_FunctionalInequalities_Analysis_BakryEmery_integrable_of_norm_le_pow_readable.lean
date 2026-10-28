-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_of_norm_le_pow_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:05.619431+00:00
-- url     : https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db
-- title:
--   Polynomial Growth Implies Integrability
-- statement:
--   This theorem gives integrability of a vector-valued function under all exponential moments.
--
--   Let $E$ be a measurable normed space, let $F$ be a normed additive group, and let $\mu$ be a measure such that $e^{r\|x\|}$ is integrable for every $r\in\mathbb R$. Suppose that $g:E\to F$ is strongly measurable almost everywhere and that, for some $C\in\mathbb R$ and $k\in\mathbb N$,
--
--   $$\|g(x)\|\le C(1+\|x\|)^k\qquad\text{for every }x\in E.$$
--
--   Then $g$ is integrable with respect to $\mu$. The result is a general domination lemma for polynomially bounded functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_of_norm_le_pow {F : Type*} [NormedAddCommGroup F] (μ : Measure E)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → F}
--       (hg : AEStronglyMeasurable g μ) {C : ℝ} {k : ℕ} (hgb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
--       Integrable g μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Temperate`](https://prove2.me/theorems/2dcac3f7-3919-472b-8b13-591e955577ca).
--
--   Previous: [`abs_laplacian_le`](https://prove2.me/theorems/f6e58a8e-3f46-421d-a064-a1f1705fd429) · Next: [`integral_weightedLaplacian_eq_zero_of_growth`](https://prove2.me/theorems/43e73809-b964-4849-8ee0-2937a72e6eac).
--
--   [Source excerpt, lines 226–229](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L226-L229) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L224-L263 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_of_norm_le_pow_readable {F : Type*} [NormedAddCommGroup F] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {C : ℝ} {k : ℕ} (hgb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Integrable g μ := by sorry
