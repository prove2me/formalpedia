-- Prove2me | Theorems.Thm_GlobalTheory_QFam_hasQ_iff_hasQExpansion_mk
-- name    : GlobalTheory.QFam.hasQ_iff_hasQExpansion_mk
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:59:49.998613+00:00
-- url     : https://prove2.me/theorems/ecd67acf-7fb7-4e62-af4d-9b9fa924941e
-- title:
--   QFam: has Q iff has QExpansion mk
-- statement:
--   The QFam construction uses the has Q iff has QExpansion mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQCoeffIffHasQExpansion.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQCoeffIffHasQExpansion.lean#L9-L13

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

theorem GlobalTheory.QFam.hasQ_iff_hasQExpansion_mk (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk a) := by sorry
