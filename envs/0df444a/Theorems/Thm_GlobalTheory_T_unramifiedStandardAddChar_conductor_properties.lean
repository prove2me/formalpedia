-- Prove2me | Theorems.Thm_GlobalTheory_T_unramifiedStandardAddChar_conductor_properties
-- name    : GlobalTheory.T.unramifiedStandardAddChar_conductor_properties
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:05.652315+00:00
-- url     : https://prove2.me/theorems/96a13d5c-ab84-4e56-810b-4bb9f82203c9
-- title:
--   T: unramified Standard Add Char conductor properties
-- statement:
--   The T construction uses the unramified Standard Add Char conductor properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedStandardAddCharConductorPropertiesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedStandardAddCharConductorPropertiesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
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

theorem GlobalTheory.T.unramifiedStandardAddChar_conductor_properties : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ → IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧ (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by sorry
