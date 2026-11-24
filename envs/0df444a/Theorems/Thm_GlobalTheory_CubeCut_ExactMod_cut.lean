-- Prove2me | Theorems.Thm_GlobalTheory_CubeCut_ExactMod_cut
-- name    : GlobalTheory.CubeCut.ExactMod.cut
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:07.470139+00:00
-- url     : https://prove2.me/theorems/c425582d-4a90-47ac-b332-6c8033755984
-- title:
--   Exact Mod: cut
-- statement:
--   The Exact Mod construction uses the cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L115-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L115-L135

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

theorem GlobalTheory.CubeCut.ExactMod.cut {A B : Cube.{0} I K} {JA : ∀ s, Submodule K (A.obj s)}
    {JB J : ∀ s, Submodule K (B.obj s)} (φ : A ⟶ B) (hA : ExactMod A JA) (hB : ExactMod B JB)
    (hJB : ∀ {s t : Finset I} (h : s ⊆ t) (x : B.obj s), x ∈ JB s → Cube.res B h x ∈ JB t)
    (hφ : ∀ s x, x ∈ JA s → (φ.app s).hom x ∈ JB s)
    (hinj : ∀ s, s.Nonempty → ∀ x, (φ.app s).hom x ∈ JB s → x ∈ JA s)
    (hJ : ∀ s, J s = JB s ⊔ LinearMap.range (φ.app s).hom) : ExactMod B J := by sorry
