-- Prove2me | Theorems.Thm_GlobalTheory_QFam_QAllSubring_sub
-- name    : GlobalTheory.QFam.QAllSubring.sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:12:19.209254+00:00
-- url     : https://prove2.me/theorems/3722f4ff-737b-46f5-bc5b-f82ccecfcf15
-- title:
--   QAll Subring: sub
-- statement:
--   The QAll Subring construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionCoeffsInSubringRingClosed.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionCoeffsInSubringRingClosed.lean#L41-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionCoeffsInSubringRingClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam GlobalTheory.QFam.QAllSubring
variable {R : Subring ℂ} {N : ℕ}
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
variable {R : Subring ℂ} {N : ℕ}

theorem GlobalTheory.QFam.QAllSubring.sub {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ := by sorry
