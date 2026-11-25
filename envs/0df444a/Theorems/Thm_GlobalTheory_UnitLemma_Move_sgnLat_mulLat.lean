-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Move_sgnLat_mulLat
-- name    : GlobalTheory.UnitLemma.Move.sgnLat_mulLat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:29:09.160498+00:00
-- url     : https://prove2.me/theorems/776a1a05-48b6-4b1c-bfa4-7c9870977f6b
-- title:
--   Move: sgn Lat mul Lat
-- statement:
--   The Move construction uses the sgn Lat mul Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SignedInvolutionStableLatticeSumMulFixedUnit.lean#L84-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SignedInvolutionStableLatticeSumMulFixedUnit.lean#L84-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SgnLatSpanBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixedBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SignedInvolutionStableLatticeSumMulFixedUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Move
variable {K : UQ} (B : InvAlg K)

theorem GlobalTheory.UnitLemma.Move.sgnLat_mulLat (hP : B.P.Separable) (M : Submodule K.O B.A) (hM : IsLat K.O K.E M)
    (hσ : ∀ y ∈ M, B.σ y ∈ M) (y : B.Aˣ) :
    B.sgnLat (mulLat K.O (y : B.A) M) = K.eta (Algebra.norm K.E (y : B.A)) * B.sgnLat M := by sorry
