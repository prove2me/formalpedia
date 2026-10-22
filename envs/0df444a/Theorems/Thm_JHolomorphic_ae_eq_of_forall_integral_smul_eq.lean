-- Prove2me | Theorems.Thm_JHolomorphic_ae_eq_of_forall_integral_smul_eq
-- name    : JHolomorphic.ae_eq_of_forall_integral_smul_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:40:16.673842+00:00
-- url     : https://prove2.me/theorems/b96e2a76-acb3-43fc-bcf1-6706225d7fad
-- title:
--   Maps with equal integrals against all test functions on an open planar set agree almost everywhere
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open and let $f,f':\mathbb{C}\to E$ be integrable on every compact subset of $U$. If $\int\varphi f=\int\varphi f'$ for every real $C^\infty$ function $\varphi$ with compact support in $U$, then $f=f'$ almost everywhere on $U$.
--
--   **Formalization Note** $E$ is a finite-dimensional real normed space; almost everywhere on $U$ is `∀ᵐ z ∂(volume.restrict U)`.
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

/-- Two maps that are integrable on every compact subset of an open set `U` and have the same
integrals against every real `C^∞` function with compact support in `U` agree almost everywhere
on `U`. -/
theorem ae_eq_of_forall_integral_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {f f' : ℂ → E}
    (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K)
    (hf' : ∀ K ⊆ U, IsCompact K → IntegrableOn f' K)
    (hφ : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ z, φ z • f z = ∫ z, φ z • f' z) :
    ∀ᵐ z ∂(volume.restrict U), f z = f' z := by
  sorry

end JHolomorphic
