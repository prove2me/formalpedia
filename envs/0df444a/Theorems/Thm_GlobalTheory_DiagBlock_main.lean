-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_main
-- name    : GlobalTheory.DiagBlock.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:56:16.434847+00:00
-- url     : https://prove2.me/theorems/b226f9a4-77b6-44ef-8725-88d32c2ebdfa
-- title:
--   Diag Block: main
-- statement:
--   The Diag Block construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L505-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L505-L505

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Theorems.Thm_GlobalTheory_DetPowPairing_main
import Theorems.Thm_GlobalTheory_UnitCase_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock

theorem GlobalTheory.DiagBlock.main : DetPowDiag ∧ BlockJet ∧ RestrictMul ∧ RestrictExp := by sorry
