-- Prove2me | Theorems.Thm_GlobalTheory_QFam_hasQ_coeff_iff_hasQExpansion
-- name    : GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:01.754056+00:00
-- url     : https://prove2.me/theorems/0d1c6174-774a-43aa-82a3-a895c4e1ecd4
-- title:
--   QFam: has Q coeff iff has QExpansion
-- statement:
--   The QFam construction uses the has Q coeff iff has QExpansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQCoeffIffHasQExpansion.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQCoeffIffHasQExpansion.lean#L17-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQCoeffIffHasQExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

theorem GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion (N : ℕ) (f : ℍ → ℂ) (φ : PowerSeries ℂ) :
    _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n φ) ↔
      _root_.GlobalTheory.HasQExpansion (N : ℝ) f φ := by sorry
