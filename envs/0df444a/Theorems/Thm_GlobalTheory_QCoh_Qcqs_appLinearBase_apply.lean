-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
-- name    : GlobalTheory.QCoh.Qcqs.appLinearBase_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:13.316184+00:00
-- url     : https://prove2.me/theorems/a0d7f060-7d63-48f5-acf2-7de229ae74ea
-- title:
--   Qcqs: app Linear Base apply
-- statement:
--   The Qcqs construction uses the app Linear Base apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L63-L65

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

theorem GlobalTheory.QCoh.Qcqs.appLinearBase_apply (p : X ⟶ Spec R) (g : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (U : X.Opens) (s : Γ(F, U)) :
    appLinearBase p g φ U s = φ.app U s := by sorry

attribute [defeq] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
