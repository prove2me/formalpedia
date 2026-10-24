-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_mul_408915f
-- name    : FunctionalInequalities.Probability.Diffusion.diffusionGenerator_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:07:57.442986+00:00
-- url     : https://prove2.me/theorems/7c8dc9f8-2310-4444-81b8-ca8e7a1e06bb
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L308-L350 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, declaration `FunctionalInequalities.Probability.Diffusion.diffusionGenerator_mul`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_mul_408915f {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (b : V → V) (σ : V → Fin d → V) {u v : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    diffusionGenerator b σ (fun y => u y * v y) x =
      u x * diffusionGenerator b σ v x + v x * diffusionGenerator b σ u x +
        ∑ k, fderiv ℝ u x (σ x k) * fderiv ℝ v x (σ x k) := by sorry
