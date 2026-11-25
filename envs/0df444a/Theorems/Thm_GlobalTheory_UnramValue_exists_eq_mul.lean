-- Prove2me | Theorems.Thm_GlobalTheory_UnramValue_exists_eq_mul
-- name    : GlobalTheory.UnramValue.exists_eq_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:59.729787+00:00
-- url     : https://prove2.me/theorems/56d63930-845f-41ee-99c1-c33507762763
-- title:
--   Unram Value: exists eq mul
-- statement:
--   The Unram Value construction uses the exists eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L129-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfield.lean#L129-L159

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

theorem GlobalTheory.UnramValue.exists_eq_mul {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) {y : Om l} (hy : y ∈ rootRing l m)
    (h1 : ‖y‖ < 1) : ∃ z ∈ rootRing l m, y = l * z := by sorry
