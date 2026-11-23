-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_algebraMap
-- name    : GlobalTheory.QCoh.Qcqs.baseRingHom_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:16.772402+00:00
-- url     : https://prove2.me/theorems/74cf2b4a-37fe-4f8e-9c23-fce752952834
-- title:
--   Qcqs: base Ring Hom algebra Map
-- statement:
--   The Qcqs construction uses the base Ring Hom algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L87-L89

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

theorem GlobalTheory.QCoh.Qcqs.baseRingHom_algebraMap (V : Y.Opens) (r : R) :
    baseRingHom q V (algebraMap R L r) = baseRingHom (g ≫ p) V r := by sorry
