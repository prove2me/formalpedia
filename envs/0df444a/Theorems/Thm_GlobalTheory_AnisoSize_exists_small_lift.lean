-- Prove2me | Theorems.Thm_GlobalTheory_AnisoSize_exists_small_lift
-- name    : GlobalTheory.AnisoSize.exists_small_lift
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:58:13.354842+00:00
-- url     : https://prove2.me/theorems/ccbae3c5-f93c-4135-81dd-e586438c8d37
-- title:
--   Aniso Size: exists small lift
-- statement:
--   The Aniso Size construction uses the exists small lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L188-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L188-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {V : Type} [AddCommGroup V] [Module E V]
  {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B : ℝ}

theorem GlobalTheory.AnisoSize.exists_small_lift [FiniteDimensional E V] (H : Sized h Λ N ν B) {C U : ℝ}
    (hC : ∀ c : E, ∃ t : E, IsIntegral ℤ t ∧ house (c - t) ≤ C) (hU : 2 ≤ U) (hB : B ≤ U ^ 1)
    (hn : (finrank E V : ℝ) ≤ U ^ 1) (hCU : C ≤ U ^ 1) {v x₀ w : V} (hv : v ∈ Λ) (hx₀ : x₀ ∈ Λ)
    (hw : w ∈ Λ) (hvU : ν v ≤ U ^ 1) (hx₀U : ν x₀ ≤ U ^ 1) (ha : h x₀ v ≠ 0)
    (haU : house (h x₀ v)⁻¹ ≤ U ^ 1) (hwU : house (h w v) ≤ U ^ 1) :
    ∃ w' ∈ Λ, h w' v = h w v ∧ ν w' ≤ U ^ 7 := by sorry
