-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_openCompact_annihilator_scaled_integersK
-- name    : GlobalTheory.T.exists_openCompact_annihilator_scaled_integersK
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:36:50.605059+00:00
-- url     : https://prove2.me/theorems/a0a43399-0882-4f08-a850-218c8cacfd22
-- title:
--   T: exists open Compact annihilator scaled integers K
-- statement:
--   The T construction uses the exists open Compact annihilator scaled integers K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOpenCompactAnnihilatorScaledIntegersKStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOpenCompactAnnihilatorScaledIntegersKStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOpenCompactAnnihilatorScaledIntegersK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOpenCompactAnnihilatorScaledIntegersKStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_openCompact_annihilator_scaled_integersK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ c : F, c ≠ 0 → ∃ D : AddSubgroup A.K, (D : Set A.K) = {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} ∧ IsOpen (D : Set A.K) ∧ IsCompact (D : Set A.K) := by sorry
