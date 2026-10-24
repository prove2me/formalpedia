-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_comp_of_contDiffAt_408915f
-- name    : FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_of_contDiffAt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:18:37.805526+00:00
-- url     : https://prove2.me/theorems/d004d4d5-8903-4863-bc13-4d6e48283513
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L240-L298 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, declaration `FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_of_contDiffAt`; the repository is private at upload time).

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
section S3B1LLocalChainRule
section NormedSpace
variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_comp_of_contDiffAt_408915f {d : ℕ} (b : V → V) (σ : V → Fin d → V)
    (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiffAt ℝ 2 Φ (G x)) (hG : ContDiffAt ℝ 2 G x) :
    diffusionGenerator b σ (Φ ∘ G) x =
      fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
          (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by sorry
