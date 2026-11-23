-- Prove2me | Theorems.Thm_GlobalTheory_T_isLocallyConstantCompactSupport_idempotentCoordinates_iff
-- name    : GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:09.56465+00:00
-- url     : https://prove2.me/theorems/525475d1-3a01-450b-9202-c99a9a20e5e1
-- title:
--   T: is Locally Constant Compact Support idempotent Coordinates iff
-- statement:
--   The T construction uses the is Locally Constant Compact Support idempotent Coordinates iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportIdempotentCoordinStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantCompactSupportIdempotentCoordinStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportIdempotentCoordin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportIdempotentCoordinStatement
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

theorem GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by sorry
