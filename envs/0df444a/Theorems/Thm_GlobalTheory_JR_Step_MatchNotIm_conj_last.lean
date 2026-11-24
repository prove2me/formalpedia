-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_conj_last
-- name    : GlobalTheory.JR.Step.MatchNotIm.conj_last
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:09.17783+00:00
-- url     : https://prove2.me/theorems/4d787faf-a53a-4ef6-8b44-16d079fe6bc5
-- title:
--   Match Not Im: conj last
-- statement:
--   The Match Not Im construction uses the conj last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasis.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasis.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.MatchNotIm
variable {r : ℕ} {k : Type} [CommRing k]

theorem GlobalTheory.JR.Step.MatchNotIm.conj_last (g g' : Matrix (Fin r) (Fin r) k) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    (embHom r k g * N * embHom r k g') (Fin.last r) (Fin.last r) = N (Fin.last r) (Fin.last r) := by sorry
