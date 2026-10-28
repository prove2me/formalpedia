-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_comp_of_contDiffAt_readable
-- name    : FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_of_contDiffAt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:20.348685+00:00
-- url     : https://prove2.me/theorems/83912579-a2cc-45d3-836f-d766607ea3b3
-- title:
--   Local Chain Rule for the Diffusion Generator
-- statement:
--   This is the local, pointwise form of the chain rule for `diffusionGenerator`.
--
--   Let $V$ and $W$ be real normed additive groups, let $d\in\mathbb N$, let $b:V\to V$, $\sigma:V\to\mathrm{Fin}(d)\to V$, $\Phi:W\to\mathbb R$, $G:V\to W$, and $x\in V$. Assume only that $\Phi$ is $C^2$ at $G(x)$ and $G$ is $C^2$ at $x$, namely `ContDiffAt ℝ 2 Φ (G x)` and `ContDiffAt ℝ 2 G x`.
--
--   With $\sigma_k(x)=\sigma(x,k)$,
--
--   $$
--   \mathcal L(\Phi\circ G)(x)=D\Phi(Gx)\left[DG(x)b(x)+\frac12\sum_kD^2G(x)[\sigma_k(x),\sigma_k(x)]\right]+\frac12\sum_kD^2\Phi(Gx)[DG(x)\sigma_k(x),DG(x)\sigma_k(x)].
--   $$
--
--   This local variant avoids global smoothness assumptions and can be reused whenever only the behavior at one state point is available.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem diffusionGenerator_comp_of_contDiffAt {d : ℕ} (b : V → V) (σ : V → Fin d → V)
--       (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiffAt ℝ 2 Φ (G x)) (hG : ContDiffAt ℝ 2 G x) :
--       diffusionGenerator b σ (Φ ∘ G) x =
--         fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
--             (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
--           (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k))
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Previous: [`diffusionGenerator_comp`](https://prove2.me/theorems/04591c87-9e70-47ad-8801-7d7fe84bea55) · Next: [`diffusionGenerator_mul`](https://prove2.me/theorems/2d42e13d-4529-4774-b00a-37bb995a10d9).
--
--   [Source excerpt, lines 243–248](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L243-L248) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L240-L298 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, declaration `FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_of_contDiffAt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_of_contDiffAt_readable {d : ℕ} (b : V → V) (σ : V → Fin d → V)
    (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiffAt ℝ 2 Φ (G x)) (hG : ContDiffAt ℝ 2 G x) :
    diffusionGenerator b σ (Φ ∘ G) x =
      fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
          (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by sorry
