-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Diffusion_vectorGenerator_clm_comp_408915f
-- name    : FunctionalInequalities.Probability.Diffusion.vectorGenerator_clm_comp_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:16:35.505663+00:00
-- url     : https://prove2.me/theorems/87f8368b-019e-4ee1-95ba-ab09d4830833
-- title:
--   Vector Generator Commutation with Continuous Linear Maps
-- statement:
--   This is a compatibility identity for the vector-valued diffusion generator under a continuous linear map.
--
--   Let $V$, $W$, and $W'$ be real normed additive groups and normed spaces, let $d$ be a natural number, let $b:V\to V$ and $\sigma:V\to\operatorname{Fin}(d)\to V$, and let $\ell:W\to W'$ be a continuous linear map. For $G:V\to W$ and $x\in V$, assume that $G$ is twice continuously differentiable at $x$.
--
--   Then, writing `vectorGenerator` for the generator,
--
--   $$
--   \operatorname{vectorGenerator}_{b,\sigma}(\ell\circ G)(x)
--   =\ell\!\left(\operatorname{vectorGenerator}_{b,\sigma}(G)(x)\right).
--   $$
--
--   The result allows generator calculations for vector-valued functions to be transported through continuous linear maps, including trace and coordinate maps.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Diffusion/VectorGenerator.lean#L43-L97 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Diffusion.VectorGenerator`, declaration `FunctionalInequalities.Probability.Diffusion.vectorGenerator_clm_comp`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Diffusion_VectorGenerator
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
open scoped Topology
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
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
section NormedSpace
variable {W W' : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']

theorem FunctionalInequalities.Probability.Diffusion.vectorGenerator_clm_comp_408915f (b : V → V) (σ : V → Fin d → V)
    (ℓ : W →L[ℝ] W') {G : V → W} {x : V} (hG : ContDiffAt ℝ 2 G x) :
    vectorGenerator b σ (fun y => ℓ (G y)) x = ℓ (vectorGenerator b σ G x) := by sorry
