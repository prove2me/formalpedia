-- Prove2me | Theorems.Thm_GlobalTheory_UnramValue_norm_of_mem_Kur
-- name    : GlobalTheory.UnramValue.norm_of_mem_Kur
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:25.997317+00:00
-- url     : https://prove2.me/theorems/0a74e63f-d5f1-4e5b-988c-03c49178c99d
-- title:
--   Unram Value: norm of mem Kur
-- statement:
--   The Unram Value construction uses the norm of mem Kur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L255-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L255-L274

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
open GlobalTheory GlobalTheory.UnramValue
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.UnramValue.norm_of_mem_Kur {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by sorry
