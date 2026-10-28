-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_gammaTwo_eq_of_hasTemperateGrowth_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_gammaTwo_eq_of_hasTemperateGrowth_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:10.75623+00:00
-- url     : https://prove2.me/theorems/20ca3ebc-8fc8-4f38-9cbb-d34bdaff3674
-- title:
--   Integrated Gamma-Two Identity
-- statement:
--   This theorem gives the integrated identity relating $\Gamma_2$ to the squared weighted Laplacian.
--
--   Let $E$ be finite-dimensional and complete with a real inner product, let $m$ be an additive Haar measure, and let $V,f:E\to\mathbb R$. Assume that $V$ and $f$ have `HasTemperateGrowth`, and that every function $x\mapsto e^{r\|x\|}$ is integrable with respect to $\mu=m.\operatorname{tilted}(-V)$. Then
--
--   $$\int \Gamma_2(V,f)\,d\mu=\int (\mathcal L_Vf)^2\,d\mu.$$
--
--   The definitions `gammaTwo` and `weightedLaplacian` are used for $\Gamma_2$ and $\mathcal L_V$. This identity is the integrated generator form underlying the Bochner formula.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_gammaTwo_eq_of_hasTemperateGrowth {V f : E → ℝ} (hV : V.HasTemperateGrowth)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
--       (hf : f.HasTemperateGrowth) :
--       ∫ x, gammaTwo V f x ∂(m.tilted (-V)) = ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Bochner/Temperate`](https://prove2.me/theorems/3d0b9fbe-846b-4821-b768-fdcecccd6374).
--
--   Definition modules: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4), [`Analysis/BakryEmery/Gamma`](https://prove2.me/theorems/6b6aef00-0f84-4633-a830-e04239f02b6b).
--
--   Supporting theorems: [`integrable_of_norm_le_pow`](https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db), [`integral_weightedLaplacian_eq_zero_of_growth`](https://prove2.me/theorems/43e73809-b964-4849-8ee0-2937a72e6eac), [`integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth`](https://prove2.me/theorems/4b2c3c7b-c447-49e8-8a0e-99319495a94d).
--
--   Next: [`integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth`](https://prove2.me/theorems/60f35586-717a-4f01-a5d5-ebcf392e454c).
--
--   [Source excerpt, lines 147–150](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Temperate.lean#L147-L150) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Temperate.lean#L146-L168 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_gammaTwo_eq_of_hasTemperateGrowth`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Temperate

open MeasureTheory Filter Topology
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_gammaTwo_eq_of_hasTemperateGrowth_readable {V f : E → ℝ} (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) :
    ∫ x, gammaTwo V f x ∂(m.tilted (-V)) = ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) := by sorry
