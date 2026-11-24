-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_finsum_le_oneValue_finrank
-- name    : GlobalTheory.CuspGL.finsum_le_oneValue_finrank
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:32:59.447326+00:00
-- url     : https://prove2.me/theorems/83566a23-132a-4545-9ced-947a28e3f63b
-- title:
--   Cusp GL: finsum le one Value finrank
-- statement:
--   The Cusp GL construction uses the finsum le one Value finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MobiusInversionAffineFinrankSubspaces.lean#L6-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MobiusInversionAffineFinrankSubspaces.lean#L6-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusInversionAffineFinrankSubspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.finsum_le_oneValue_finrank (K : Type) [Field K] [Finite K] (U : Type) [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (A : Submodule K U) :
    ∑ᶠ B : {B : Submodule K U // B ≤ A}, oneValue (Nat.card K) (Module.finrank K B.1) =
      (Module.finrank K A : ℂ) := by sorry
