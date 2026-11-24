-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Move_term_mulLat
-- name    : GlobalTheory.UnitLemma.Move.term_mulLat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:40.264672+00:00
-- url     : https://prove2.me/theorems/220c5853-6812-4bd9-a2dc-554820f98380
-- title:
--   Move: term mul Lat
-- statement:
--   The Move construction uses the term mul Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SignedInvolutionStableLatticeSumMulFixedUnit.lean#L126-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SignedInvolutionStableLatticeSumMulFixedUnit.lean#L126-L140

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

theorem GlobalTheory.UnitLemma.Move.term_mulLat {ι : Type} (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A)
    (y : B.Aˣ) :
    term B π I I' ((y : B.A) * u) s (mulLat K.O (y : B.A) M) = term B π I I' u ((y : B.A) * s) M := by sorry
