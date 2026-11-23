-- Prove2me | Theorems.Thm_GlobalTheory_UnramValue_norm_l
-- name    : GlobalTheory.UnramValue.norm_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:49.194163+00:00
-- url     : https://prove2.me/theorems/2685e1bf-de5e-4683-9e06-51b39681d458
-- title:
--   Unram Value: norm l
-- statement:
--   The Unram Value construction uses the norm l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L20-L22

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

theorem GlobalTheory.UnramValue.norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by sorry
