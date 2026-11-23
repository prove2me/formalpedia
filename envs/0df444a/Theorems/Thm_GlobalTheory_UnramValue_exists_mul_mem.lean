-- Prove2me | Theorems.Thm_GlobalTheory_UnramValue_exists_mul_mem
-- name    : GlobalTheory.UnramValue.exists_mul_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:31.400058+00:00
-- url     : https://prove2.me/theorems/c7d506b8-f88b-4834-a368-d1279a8787b8
-- title:
--   Unram Value: exists mul mem
-- statement:
--   The Unram Value construction uses the exists mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L193-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L193-L253

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

theorem GlobalTheory.UnramValue.exists_mul_mem {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ∃ c : ℤ_[l], c ≠ 0 ∧ algebraMap ℤ_[l] (Om l) c * x ∈ rootRing l m := by sorry
