-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:12.126846+00:00
-- url     : https://prove2.me/theorems/60f35586-717a-4f01-a5d5-ebcf392e454c
-- title:
--   Integrated Bochner Formula
-- statement:
--   Let $E$ be finite-dimensional and complete with a real inner product, let $m$ be an additive Haar measure, and let $V,f:E\to\mathbb R$. Assume that $V$ and $f$ have `HasTemperateGrowth`, and that every exponential moment is integrable for $\mu=m.\operatorname{tilted}(-V)$. Then
--
--   $$\int (\mathcal L_Vf)^2\,d\mu
--   =\int \|D^2f\|_{\mathrm{HS}}^2\,d\mu
--   +\int D^2V[\nabla f,\nabla f]\,d\mu.$$
--
--   In the formalization, `hessianSqStdBasis f` represents the squared Hessian Hilbert–Schmidt norm in the standard orthonormal basis, while `bilinearIteratedFDerivTwo` represents the Hessian bilinear form. This is the integrated Bochner identity on the temperate-growth class.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth {V f : E → ℝ}
--       (hV : V.HasTemperateGrowth)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
--       (hf : f.HasTemperateGrowth) :
--       ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) =
--         ∫ x, hessianSqStdBasis f x ∂(m.tilted (-V)) +
--           ∫ x, bilinearIteratedFDerivTwo ℝ V x (gradient f x) (gradient f x) ∂(m.tilted (-V))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Bochner/Temperate`](https://prove2.me/theorems/3d0b9fbe-846b-4821-b768-fdcecccd6374).
--
--   Definition modules: [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a), [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Supporting theorems: [`gammaTwo_eq_hessianSqStdBasis_add`](https://prove2.me/theorems/179f18c6-eedc-4764-b606-7f97a6d4c71b), [`integrable_of_norm_le_pow`](https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db), [`integral_gammaTwo_eq_of_hasTemperateGrowth`](https://prove2.me/theorems/20ca3ebc-8fc8-4f38-9cbb-d34bdaff3674).
--
--   Previous: [`integral_gammaTwo_eq_of_hasTemperateGrowth`](https://prove2.me/theorems/20ca3ebc-8fc8-4f38-9cbb-d34bdaff3674) · Next: [`integral_hessianSq_add_le_of_hasTemperateGrowth`](https://prove2.me/theorems/fcac2fc2-d13a-43a7-b290-c7c1b8a429f0).
--
--   [Source excerpt, lines 189–195](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Temperate.lean#L189-L195) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Equation (16) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited as Equation (16), p. 6.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (16), p. 6 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Temperate.lean#L187-L215 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Temperate

open MeasureTheory Filter Topology
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth_readable {V f : E → ℝ}
    (hV : V.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) :
    ∫ x, weightedLaplacian V f x ^ 2 ∂(m.tilted (-V)) =
      ∫ x, hessianSqStdBasis f x ∂(m.tilted (-V)) +
        ∫ x, bilinearIteratedFDerivTwo ℝ V x (gradient f x) (gradient f x) ∂(m.tilted (-V)) := by sorry
