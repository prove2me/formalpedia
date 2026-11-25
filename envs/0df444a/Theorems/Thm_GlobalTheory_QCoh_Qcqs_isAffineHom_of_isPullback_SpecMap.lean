-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_isAffineHom_of_isPullback_SpecMap
-- name    : GlobalTheory.QCoh.Qcqs.isAffineHom_of_isPullback_SpecMap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:38.340838+00:00
-- url     : https://prove2.me/theorems/ad0704c8-d903-4091-9578-eb6c8e51bc19
-- title:
--   Qcqs: is Affine Hom of is Pullback Spec Map
-- statement:
--   The Qcqs construction uses the is Affine Hom of is Pullback Spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L92-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {R L : CommRingCat.{u}} [Algebra R L] (S : Submonoid R) [IsLocalization S L]
  {X Y : Scheme.{u}} {p : X ⟶ Spec R} {q : Y ⟶ Spec L} {g : Y ⟶ X}
  (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R L))))
include H
omit S

theorem GlobalTheory.QCoh.Qcqs.isAffineHom_of_isPullback_SpecMap : IsAffineHom g := by sorry
