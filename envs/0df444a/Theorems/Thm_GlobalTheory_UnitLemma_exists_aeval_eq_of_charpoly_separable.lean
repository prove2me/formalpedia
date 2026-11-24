-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_exists_aeval_eq_of_charpoly_separable
-- name    : GlobalTheory.UnitLemma.exists_aeval_eq_of_charpoly_separable
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:31:19.596039+00:00
-- url     : https://prove2.me/theorems/b48f7d4e-bcc1-423c-84ed-452202c40f8c
-- title:
--   Unit Lemma: exists aeval eq of charpoly separable
-- statement:
--   The Unit Lemma construction uses the exists aeval eq of charpoly separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfCharpolySeparableInvolution.lean#L8-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfCharpolySeparableInvolution.lean#L8-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.exists_aeval_eq_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) (a : A) :
    ∃ f : E[X], a = aeval g f := by sorry
