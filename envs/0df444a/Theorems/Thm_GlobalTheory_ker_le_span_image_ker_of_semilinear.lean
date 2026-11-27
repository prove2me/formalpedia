-- Prove2me | Theorems.Thm_GlobalTheory_ker_le_span_image_ker_of_semilinear
-- name    : GlobalTheory.ker_le_span_image_ker_of_semilinear
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:08.226394+00:00
-- url     : https://prove2.me/theorems/83f35e07-b5a0-5c15-a26e-249db2992bd6
-- title:
--   Global Theory: ker le span image ker of semilinear
-- statement:
--   The Global Theory construction uses the ker le span image ker of semilinear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerLeSpanImageKerOfSemilinear.lean#L6-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerLeSpanImageKerOfSemilinear.lean#L6-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerLeSpanImageKerOfSemilinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.ker_le_span_image_ker_of_semilinear :
    ∀ (K X Y H W : Type) [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y] [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W), Submodule.span ℂ (Set.range j) = ⊤ → (∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k)) → (∀ x, T (j x) = jW (θ x)) → LinearMap.ker T ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := by sorry
