-- Prove2me | Theorems.Thm_GlobalTheory_UnramValue_norm_of_mem_unramified_subfield
-- name    : GlobalTheory.UnramValue.norm_of_mem_unramified_subfield
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:34.29841+00:00
-- url     : https://prove2.me/theorems/4ca2ae43-ed23-4411-a107-dfbee69db282
-- title:
--   Unram Value: norm of mem unramified subfield
-- statement:
--   The Unram Value construction uses the norm of mem unramified subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L276-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L276-L280

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

theorem GlobalTheory.UnramValue.norm_of_mem_unramified_subfield : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : Om l),
    x ∈ K0 K → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by sorry
