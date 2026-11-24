-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_conj_pow
-- name    : GlobalTheory.JR.Step.MatchNotIm.conj_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:52.020822+00:00
-- url     : https://prove2.me/theorems/45766d0e-35e1-4399-b073-72cc5c0473b1
-- title:
--   Match Not Im: conj pow
-- statement:
--   The Match Not Im construction uses the conj pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasis.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasis.lean#L62-L69

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

theorem GlobalTheory.JR.Step.MatchNotIm.conj_pow {n : Type} [Fintype n] [DecidableEq n] {k : Type} [CommRing k] (P Q N : Matrix n n k)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (i : ℕ) : (P * N * Q) ^ i = P * N ^ i * Q := by sorry
