-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionCoeffs_lipschitz_readable
-- name    : FunctionalInequalities.Probability.Diffusion.diffusionCoeffs_lipschitz_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:21.24713+00:00
-- url     : https://prove2.me/theorems/fd8b709d-67fc-4441-99f2-2be39c9c9a73
-- title:
--   Lipschitz Bound For Transported Diffusion Coefficients
-- statement:
--   This auxiliary lemma concerns autonomous coefficients. Let $b:(\mathbb R^N)\to\mathbb R^N$ and $\sigma:(\mathbb R^N)\to(\mathbb R^d\to\mathbb R^N)$, and let $K\in[0,\infty)$ be an `NNReal`. If $b$ is $K$-Lipschitz and every map $x\mapsto\sigma(x,k)$ is $K$-Lipschitz, then there exists $L\in\mathbb R$ such that the corresponding `diffusionCoeffs b σ` are `IsLipschitz` with respect to the zero measure on the unit space:
--
--   $$\exists L,\quad \operatorname{IsLipschitz}(\operatorname{diffusionCoeffs}(b,\sigma),0,L).$$
--
--   This declaration serves as a technical bridge from componentwise Lipschitz hypotheses to the bundled coefficient condition.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem diffusionCoeffs_lipschitz {N d : ℕ}
--       {b : (Fin N → ℝ) → Fin N → ℝ}
--       {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {K : ℝ≥0}
--       (hb : LipschitzWith K b) (hσ : ∀ k, LipschitzWith K fun x => σ x k) :
--       ∃ L : ℝ, (diffusionCoeffs b σ).IsLipschitz (0 : Measure Unit) L
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/Existence`](https://prove2.me/theorems/523c289a-088b-456f-9966-2cf2f32eb8dc).
--
--   Definition modules: [`LevyStochCalc/Ito/Setting`](https://prove2.me/theorems/791dec12-d4eb-42e1-82f3-a7db61af16a7).
--
--   Next: [`exists_isDiffusion`](https://prove2.me/theorems/7af98979-05ab-4014-86ce-c2315b88e573).
--
--   [Source excerpt, lines 109–113](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Existence.lean#L109-L113) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Existence.lean#L109-L154 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Existence`, declaration `_private.FunctionalInequalities.Probability.Diffusion.Existence.0.FunctionalInequalities.Probability.Diffusion.diffusionCoeffs_lipschitz`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Existence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem FunctionalInequalities.Probability.Diffusion.diffusionCoeffs_lipschitz_readable {N d : ℕ}
    {b : (Fin N → ℝ) → Fin N → ℝ}
    {σ : (Fin N → ℝ) → Fin d → Fin N → ℝ} {K : ℝ≥0}
    (hb : LipschitzWith K b) (hσ : ∀ k, LipschitzWith K fun x => σ x k) :
    ∃ L : ℝ, (FunctionalInequalities.Probability.Diffusion.diffusionCoeffs b σ).IsLipschitz (0 : Measure Unit) L := by sorry
