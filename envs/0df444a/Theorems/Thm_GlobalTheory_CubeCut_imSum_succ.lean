-- Prove2me | Theorems.Thm_GlobalTheory_CubeCut_imSum_succ
-- name    : GlobalTheory.CubeCut.imSum_succ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:13.423407+00:00
-- url     : https://prove2.me/theorems/899b74c9-377c-4355-9a5a-5c285c59c259
-- title:
--   Cube Cut: im Sum succ
-- statement:
--   The Cube Cut construction uses the im Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L157-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/CubeCutRegularSequence.lean#L157-L167

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

theorem GlobalTheory.CubeCut.imSum_succ (i : Fin g) (s : Finset I) :
    imSum φ (i + 1) s = imSum φ i s ⊔ LinearMap.range ((φ i).app s).hom := by sorry
