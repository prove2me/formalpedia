-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_top
-- name    : GlobalTheory.QCoh.Qcqs.baseRingHom_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:59.019133+00:00
-- url     : https://prove2.me/theorems/758d4c7e-a8cd-4df1-b8e7-7c06729a918e
-- title:
--   Qcqs: base Ring Hom top
-- statement:
--   The Qcqs construction uses the base Ring Hom top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineHomOfIsPullbackSpecMap.lean#L25-L28

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

theorem GlobalTheory.QCoh.Qcqs.baseRingHom_top (p : X ⟶ Spec R) :
    baseRingHom p ⊤ = (Scheme.ΓSpecIso R).inv ≫ p.appTop := by sorry
