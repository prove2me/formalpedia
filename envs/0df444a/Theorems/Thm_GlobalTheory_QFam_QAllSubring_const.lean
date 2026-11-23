-- Prove2me | Theorems.Thm_GlobalTheory_QFam_QAllSubring_const
-- name    : GlobalTheory.QFam.QAllSubring.const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:33.986275+00:00
-- url     : https://prove2.me/theorems/0157d75a-2053-4fc9-ac17-2fb03d528f08
-- title:
--   QAll Subring: const
-- statement:
--   The QAll Subring construction uses the const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionCoeffsInSubringRingClosed.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionCoeffsInSubringRingClosed.lean#L13-L25

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

theorem GlobalTheory.QFam.QAllSubring.const {c : ℂ} (hc : c ∈ R) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c := by sorry
