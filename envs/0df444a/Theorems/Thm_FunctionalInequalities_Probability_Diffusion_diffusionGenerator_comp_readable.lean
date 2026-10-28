-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_comp_readable
-- name    : FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:14.414396+00:00
-- url     : https://prove2.me/theorems/04591c87-9e70-47ad-8801-7d7fe84bea55
-- title:
--   Global Chain Rule for the Diffusion Generator
-- statement:
--   This formalizes the global chain rule for `diffusionGenerator`, identified in the source as step (82) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $V$ and $W$ be real normed additive groups, let $d\in\mathbb N$, let $b:V\to V$ be a drift field, let $\sigma:V\to\mathrm{Fin}(d)\to V$ be the noise field, let $\Phi:W\to\mathbb R$, let $G:V\to W$, and let $x\in V$. Assume that $\Phi$ and $G$ are globally $C^2$ (`ContDiff ℝ 2`).
--
--   Writing $\sigma_k(x)=\sigma(x,k)$, the generator of the composite satisfies
--
--   $$
--   \mathcal L(\Phi\circ G)(x)=D\Phi(Gx)\left[DG(x)b(x)+\frac12\sum_k D^2G(x)[\sigma_k(x),\sigma_k(x)]\right]+\frac12\sum_k D^2\Phi(Gx)[DG(x)\sigma_k(x),DG(x)\sigma_k(x)].
--   $$
--
--   Here `diffusionGenerator` is the first-order drift term plus one half of the diagonal second-derivative noise sum. The statement is a reusable coordinate-free composition rule on normed spaces; it is an equality at every point, not merely almost everywhere.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Diffusion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem diffusionGenerator_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
--       [NormedAddCommGroup W] [NormedSpace ℝ W] {d : ℕ} (b : V → V) (σ : V → Fin d → V)
--       (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiff ℝ 2 Φ) (hG : ContDiff ℝ 2 G) :
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
--   Previous: [`diffusionGenerator_transport`](https://prove2.me/theorems/9a1d8a25-4515-49cd-b4f2-f5f23338d6b2) · Next: [`diffusionGenerator_comp_of_contDiffAt`](https://prove2.me/theorems/83912579-a2cc-45d3-836f-d766607ea3b3).
--
--   [Source excerpt, lines 88–94](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L88-L94) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 5.1, p. 22. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L86-L161 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, declaration `FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator

theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_readable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {d : ℕ} (b : V → V) (σ : V → Fin d → V)
    (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiff ℝ 2 Φ) (hG : ContDiff ℝ 2 G) :
    diffusionGenerator b σ (Φ ∘ G) x =
      fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
          (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by sorry
