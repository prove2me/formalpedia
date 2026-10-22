-- Prove2me | Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
-- name    : JHolomorphic.fderiv_apply_isTestFunction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:41:25.133229+00:00
-- url     : https://prove2.me/theorems/e1941b9d-946f-4196-902d-ec9ca3084990
-- title:
--   Directional derivatives of test functions on $U\subseteq\mathbb{C}$ are test functions on $U$
-- statement:
--   Let $\varphi:\mathbb{C}\to\mathbb{R}$ be $C^\infty$ with compact support contained in $U\subseteq\mathbb{C}$, and let $v\in\mathbb{C}$. Then $z\mapsto D\varphi(z)\,v$ is again $C^\infty$ with compact support contained in $U$.
--
--   **Formalization Note** $D\varphi(z)\,v$ is `fderiv ℝ φ z v`; the support conditions are `HasCompactSupport` and `tsupport · ⊆ U`.
-- source:
--   Standard (weak derivatives and distribution theory).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

/-- A directional derivative `z ↦ Dφ(z) v` of a real `C^∞` function `φ` with compact support in
`U` is again a real `C^∞` function with compact support in `U`. -/
theorem fderiv_apply_isTestFunction {U : Set ℂ} {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) ∧ HasCompactSupport (fun z => fderiv ℝ φ z v) ∧
      tsupport (fun z => fderiv ℝ φ z v) ⊆ U := by
  sorry

end JHolomorphic
