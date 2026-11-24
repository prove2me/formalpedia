-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_mem_only
-- name    : GlobalTheory.QNorm.exists_mem_only
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:02:07.576875+00:00
-- url     : https://prove2.me/theorems/6871d6d1-bfeb-42a1-809f-e5a19b1f63a4
-- title:
--   QNorm: exists mem only
-- statement:
--   The QNorm construction uses the exists mem only property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FinrankSUnitsNumberFieldAddOne.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/FinrankSUnitsNumberFieldAddOne.lean#L11-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsNumberFieldFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FinrankSUnitsNumberFieldAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.exists_mem_only (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ a ∈ v.asIdeal ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → a ∉ w.asIdeal := by sorry
