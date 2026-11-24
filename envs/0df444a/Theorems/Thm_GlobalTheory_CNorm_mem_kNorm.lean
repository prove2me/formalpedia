-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_mem_kNorm
-- name    : GlobalTheory.CNorm.mem_kNorm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:42.417449+00:00
-- url     : https://prove2.me/theorems/6dc698fc-1bd4-4500-9bcb-9cd6cfd3a21a
-- title:
--   CNorm: mem k Norm
-- statement:
--   The CNorm construction uses the mem k Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L64-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem GlobalTheory.CNorm.mem_kNorm (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L)
    (δ : F) (x : Fˣ) :
    x ∈ _root_.GlobalTheory.CNorm.kNorm p φ δ ↔ ∃ y : (AdjoinRoot (X ^ p - C (φ δ) : L[X]))ˣ,
      Algebra.norm L (y : AdjoinRoot (X ^ p - C (φ δ) : L[X])) = φ (x : F) := by sorry
