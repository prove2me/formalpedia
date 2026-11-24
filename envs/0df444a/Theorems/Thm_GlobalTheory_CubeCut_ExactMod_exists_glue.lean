-- Prove2me | Theorems.Thm_GlobalTheory_CubeCut_ExactMod_exists_glue
-- name    : GlobalTheory.CubeCut.ExactMod.exists_glue
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:00.129803+00:00
-- url     : https://prove2.me/theorems/fe4dcd64-6029-45f0-bc7b-826bb52c6950
-- title:
--   Exact Mod: exists glue
-- statement:
--   The Exact Mod construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L46-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L46-L72

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

theorem GlobalTheory.CubeCut.ExactMod.exists_glue {A : Cube.{0} I K} {J : ∀ s, Submodule K (A.obj s)}
    (h : ExactMod A J) (y : ∀ a : I, A.obj {a})
    (hy : ∀ a a' : I, Cube.res A (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) -
      Cube.res A (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ J {a, a'}) :
    ∃ y₀ : A.obj ∅, ∀ a, Cube.res A (Finset.empty_subset {a}) y₀ - y a ∈ J {a} := by sorry
