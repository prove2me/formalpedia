-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_res
-- name    : GlobalTheory.QCoh.Qcqs.baseRingHom_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:27.785082+00:00
-- url     : https://prove2.me/theorems/82d6b4f0-223f-443d-ac12-b7e802192d77
-- title:
--   Qcqs: base Ring Hom res
-- statement:
--   The Qcqs construction uses the base Ring Hom res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L20-L23

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
variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QCoh.Qcqs.baseRingHom_res (p : X ⟶ Spec R) {U V : X.Opens} (h : V ≤ U) (r : R) :
    X.presheaf.map (homOfLE h).op (baseRingHom p U r) = baseRingHom p V r := by sorry
