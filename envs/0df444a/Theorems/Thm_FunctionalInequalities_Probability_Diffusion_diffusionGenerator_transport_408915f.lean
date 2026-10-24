-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_diffusionGenerator_transport_408915f
-- name    : FunctionalInequalities.Probability.Diffusion.diffusionGenerator_transport_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:55:13.797177+00:00
-- url     : https://prove2.me/theorems/104a8107-df7b-4807-b527-66daf4ef5376
-- title:
--   Diffusion Generator Under Linear Coordinate Transport
-- statement:
--   Let $V,V'$ be finite-dimensional real normed spaces, let $\Phi:V\simeq V'$ be a continuous linear equivalence, let $b:V\to V$, $\sigma:V\to\mathrm{Fin}(d)\to V$, and $F:V\to\mathbb R$. For every $x\in V$, the generator is invariant under transport:
--
--   $$
--   \mathcal L_{\Phi_*b,\Phi_*\sigma}(F\circ\Phi^{-1})(\Phi x)
--   =\mathcal L_{b,\sigma}F(x).
--   $$
--
--   Here `transportDrift`, `transportNoise`, and `diffusionGenerator` are the Lean definitions involved. No differentiability assumption on $F$ is included in the theorem statement.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean#L44-L72 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.Generator`, declaration `FunctionalInequalities.Probability.Diffusion.diffusionGenerator_transport`; the repository is private at upload time).

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
section Adapter
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Probability.Diffusion.diffusionGenerator_transport_408915f {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    {d : ℕ} (Φ : V ≃L[ℝ] V') (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) :
    diffusionGenerator (transportDrift Φ b) (transportNoise Φ σ) (F ∘ Φ.symm) (Φ x) =
      diffusionGenerator b σ F x := by sorry
