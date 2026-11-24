-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_UNormal_full_cc
-- name    : GlobalTheory.JR.Step.UNormal.full_cc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:36:13.047215+00:00
-- url     : https://prove2.me/theorems/ef7d4db2-fa74-4e46-bdd2-be48831c1fa3
-- title:
--   UNormal: full cc
-- statement:
--   The UNormal construction uses the full cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryOrbitNormalFormUnitInvariant.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryOrbitNormalFormUnitInvariant.lean#L50-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.UNormal
variable {r : ℕ} {k : Type} [CommRing k]

theorem GlobalTheory.JR.Step.UNormal.full_cc (Y : Gl r k) (i j : Fin r) : full Y (Fin.castSucc i) (Fin.castSucc j) = Y.1 i j := by sorry
