-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_IsCyc_continuous
-- name    : GlobalTheory.Cyc.IsCyc.continuous
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:42.908947+00:00
-- url     : https://prove2.me/theorems/27b78f93-1cbc-4b17-b787-42596de47538
-- title:
--   Is Cyc: continuous
-- statement:
--   The Is Cyc construction uses the continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L78-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L78-L94

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.IsCyc.continuous {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) :
    Continuous (fun g => (χ g : ℚ_[l])) := by sorry
