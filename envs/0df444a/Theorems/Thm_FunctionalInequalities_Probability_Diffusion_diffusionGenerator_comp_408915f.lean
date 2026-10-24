-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_comp_408915f
-- name    : FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:18:37.337771+00:00
-- url     : https://prove2.me/theorems/bb7ce9d6-45a8-4a55-9f9c-43304966daaf
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
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 5.1, p. 22. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L86-L161 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, declaration `FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Fin

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Diffusion
end FunctionalInequalities.Probability.Diffusion
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Diffusion
section S3B1GeneratorChainRule

theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_408915f {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {d : ℕ} (b : V → V) (σ : V → Fin d → V)
    (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiff ℝ 2 Φ) (hG : ContDiff ℝ 2 G) :
    diffusionGenerator b σ (Φ ∘ G) x =
      fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
          (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by sorry
