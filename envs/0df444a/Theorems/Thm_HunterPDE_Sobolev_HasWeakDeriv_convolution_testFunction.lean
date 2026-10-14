-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_convolution_testFunction
-- name    : HunterPDE.Sobolev.HasWeakDeriv.convolution_testFunction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T22:58:32.563006+00:00
-- url     : https://prove2.me/theorems/9d274d54-37ee-4b4b-a8c9-38c29f130aa7
-- title:
--   Smooth compact convolution preserves weak multi-index derivatives
-- statement:
--   Let $f,d:\mathbb R^n\to\mathbb R$ be locally integrable, and suppose $d$ is the weak multi-index derivative $D^\alpha f$ on the whole space. For every smooth compactly supported scalar function $\rho$, convolution preserves this relation:
--
--   $$D^\alpha(\rho*f)=\rho*d$$
--
--   in the weak sense. In particular, both convolutions are locally integrable and satisfy the defining integration identity against every smooth compactly supported test function. There is no normalization, positivity, global integrability or Lp assumption. The statement includes order zero and dimension zero. This is the whole-space weak formulation of the mollifier commutation argument in Hunter, Theorem 3.19, generalized to arbitrary smooth compactly supported kernels.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Theorem 3.19 and proof (printed p. 55), using Theorem 1.28 (printed pp. 12–13). The arbitrary smooth compactly supported kernel and weak-formulation interface are a derived generalization; no positivity or normalization is used in the commutation argument.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Convolution

open MeasureTheory ContinuousLinearMap HunterPDE.Sobolev
open scoped Convolution

theorem HunterPDE.Sobolev.HasWeakDeriv.convolution_testFunction {n : ℕ}
    {α : Fin n → ℕ} {f d : EuclideanSpace ℝ (Fin n) → ℝ}
    (hd : HasWeakDeriv Set.univ α f d)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : IsTestFunction Set.univ ρ) :
    HasWeakDeriv Set.univ α (ρ ⋆[lsmul ℝ ℝ, volume] f)
      (ρ ⋆[lsmul ℝ ℝ, volume] d) := by sorry
