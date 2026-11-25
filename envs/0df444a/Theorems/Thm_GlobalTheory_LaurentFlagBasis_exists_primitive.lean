-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFlagBasis_exists_primitive
-- name    : GlobalTheory.LaurentFlagBasis.exists_primitive
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:45:45.010513+00:00
-- url     : https://prove2.me/theorems/fe188a35-8936-4156-9261-24002beddaf7
-- title:
--   Laurent Flag Basis: exists primitive
-- statement:
--   The Laurent Flag Basis construction uses the exists primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdaptedIntegralBasis.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdaptedIntegralBasis.lean#L13-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory GlobalTheory.LaurentFlagBasis
variable {F : Type} [Field F]

theorem GlobalTheory.LaurentFlagBasis.exists_primitive {n : ℕ} (u : Fin n → LaurentSeries F) (hu : u ≠ 0) :
    ∃ (i : Fin n) (y : Fin n → PowerSeries F), lift y = (u i)⁻¹ • u ∧ y i = 1 := by sorry
