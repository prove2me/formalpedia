-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_mul_readable
-- name    : FunctionalInequalities.Probability.Diffusion.diffusionGenerator_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:13.316996+00:00
-- url     : https://prove2.me/theorems/2d42e13d-4529-4774-b00a-37bb995a10d9
-- title:
--   Product Rule for the Diffusion Generator
-- statement:
--   This is the carré-du-champ product rule for a diffusion generator.
--
--   Let $V$ be a real normed vector space, let $b:V\to V$ be a drift field, and let $\sigma:V\to\operatorname{Fin}(d)\to V$ be the noise-column field. If $u,v:V\to\mathbb R$ are twice differentiable at $x$, then
--
--   $$\mathcal L(uv)(x)
--   =u(x)\mathcal Lv(x)+v(x)\mathcal Lu(x)
--   +\sum_{k}Du(x)[\sigma(x,k)]\,Dv(x)[\sigma(x,k)].$$
--
--   The generator `diffusionGenerator` uses the convention
--   $DF(x)[b(x)]+\frac12\sum_kD^2F(x)[\sigma(x,k),\sigma(x,k)]$. This identity is a reusable analytic rule for products of test functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem diffusionGenerator_mul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
--       (b : V → V) (σ : V → Fin d → V) {u v : V → ℝ} {x : V}
--       (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
--       diffusionGenerator b σ (fun y => u y * v y) x =
--         u x * diffusionGenerator b σ v x + v x * diffusionGenerator b σ u x +
--           ∑ k, fderiv ℝ u x (σ x k) * fderiv ℝ v x (σ x k)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Previous: [`diffusionGenerator_comp_of_contDiffAt`](https://prove2.me/theorems/83912579-a2cc-45d3-836f-d766607ea3b3).
--
--   [Source excerpt, lines 310–315](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L310-L315) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L308-L350 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, declaration `FunctionalInequalities.Probability.Diffusion.diffusionGenerator_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator

theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_mul_readable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (b : V → V) (σ : V → Fin d → V) {u v : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    diffusionGenerator b σ (fun y => u y * v y) x =
      u x * diffusionGenerator b σ v x + v x * diffusionGenerator b σ u x +
        ∑ k, fderiv ℝ u x (σ x k) * fderiv ℝ v x (σ x k) := by sorry
