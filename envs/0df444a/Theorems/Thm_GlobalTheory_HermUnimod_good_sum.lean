-- Prove2me | Theorems.Thm_GlobalTheory_HermUnimod_good_sum
-- name    : GlobalTheory.HermUnimod.good_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:20:26.187837+00:00
-- url     : https://prove2.me/theorems/ca5e291b-4946-4d70-be59-f6b134b68ed2
-- title:
--   Herm Unimod: good sum
-- statement:
--   The Herm Unimod construction uses the good sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHermitianMatrixCongruentOne.lean#L88-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHermitianMatrixCongruentOne.lean#L88-L124

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
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
open GlobalTheory GlobalTheory.HermUnimod
variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]

theorem GlobalTheory.HermUnimod.good_sum (hs : ∀ y : E, ‖star y‖ = ‖y‖) {m : Type} [Fintype m] [DecidableEq m] (H : Good m E)
    (G : Matrix (m ⊕ Unit) (m ⊕ Unit) E) (hG : G.IsHermitian) (hGi : ∀ i j, ‖G i j‖ ≤ 1)
    (hGd : ‖G.det‖ = 1) (hk : G (Sum.inr ()) (Sum.inr ()) = 1) :
    ∃ h : Matrix (m ⊕ Unit) (m ⊕ Unit) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by sorry
