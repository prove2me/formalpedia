-- Prove2me | Theorems.Thm_GlobalTheory_UnramValue_pow_sub_mem
-- name    : GlobalTheory.UnramValue.pow_sub_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:33.174737+00:00
-- url     : https://prove2.me/theorems/9bdd1666-ba2b-4cab-ba2c-7993e2567620
-- title:
--   Unram Value: pow sub mem
-- statement:
--   The Unram Value construction uses the pow sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L95-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L95-L127

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

theorem GlobalTheory.UnramValue.pow_sub_mem {m : ℕ} (hl : ¬ l ∣ m) {y : Om l} (hy : y ∈ rootRing l m) :
    ∃ z ∈ rootRing l m, y ^ (l ^ m.totient) = y + l * z := by sorry
