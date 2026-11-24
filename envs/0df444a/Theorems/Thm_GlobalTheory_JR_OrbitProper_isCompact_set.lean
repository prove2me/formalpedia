-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbitProper_isCompact_set
-- name    : GlobalTheory.JR.OrbitProper.isCompact_set
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:35:01.451898+00:00
-- url     : https://prove2.me/theorems/faebe701-6194-4a36-b2e3-a07b9d79bf2b
-- title:
--   Orbit Proper: is Compact set
-- statement:
--   The Orbit Proper construction uses the is Compact set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L146-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L146-L173

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbitProper
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem GlobalTheory.JR.OrbitProper.isCompact_set (C : Set (Gl r F)) (Ω : Set (Inv r F)) (hC : IsCompact C) (hΩ : IsCompact Ω)
    (hD : ∀ a ∈ Ω, Delta a ≠ 0) :
    IsCompact {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ C} := by sorry
