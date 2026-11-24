-- Prove2me | Theorems.Thm_GlobalTheory_CubeCut_d_mem
-- name    : GlobalTheory.CubeCut.d_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:11.230246+00:00
-- url     : https://prove2.me/theorems/bc404de8-3ccc-478e-843b-a16a95f90943
-- title:
--   Cube Cut: d mem
-- statement:
--   The Cube Cut construction uses the d mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L17-L24

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

theorem GlobalTheory.CubeCut.d_mem {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (hJ : ∀ {s t : Finset I} (h : s ⊆ t) (x : A.obj s), x ∈ J s → Cube.res A h x ∈ J t)
    {p : ℕ} {x : Cube.Term A p} (hx : ∀ s, x s ∈ J s.1) (t) : Cube.d A p x t ∈ J t.1 := by sorry
