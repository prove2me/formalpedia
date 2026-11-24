-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_IsKum_pow_apply
-- name    : GlobalTheory.CNorm.IsKum.pow_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:45.400336+00:00
-- url     : https://prove2.me/theorems/9d020875-00ad-4ca6-9940-b6bd3154720f
-- title:
--   Is Kum: pow apply
-- statement:
--   The Is Kum construction uses the pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/KummerGalois.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/KummerGalois.lean#L14-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_KummerGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.IsKum.pow_apply {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (k : ℕ) :
    (σ ^ k) θ = algebraMap F E (ζ ^ k) * θ := by sorry
