-- Prove2me | Theorems.Thm_GlobalTheory_CubeCut_res_mem_imSum
-- name    : GlobalTheory.CubeCut.res_mem_imSum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:08.466179+00:00
-- url     : https://prove2.me/theorems/368e771b-d819-4221-9dc6-2e55389134ae
-- title:
--   Cube Cut: res mem im Sum
-- statement:
--   The Cube Cut construction uses the res mem im Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L146-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L146-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory GlobalTheory
open GlobalTheory
open GlobalTheory.CubeCut
variable {K : Type} [CommRing K] {I : Type} [LinearOrder I]
variable {g : ℕ} {A B : Cube.{0} I K} (φ : Fin g → (A ⟶ B))
omit [LinearOrder I]

theorem GlobalTheory.CubeCut.res_mem_imSum (k : ℕ) {s t : Finset I} (h : s ⊆ t) (x : B.obj s)
    (hx : x ∈ imSum φ k s) : Cube.res B h x ∈ imSum φ k t := by sorry
