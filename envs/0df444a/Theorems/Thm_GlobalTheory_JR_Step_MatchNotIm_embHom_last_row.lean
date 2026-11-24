-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_embHom_last_row
-- name    : GlobalTheory.JR.Step.MatchNotIm.embHom_last_row
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:16.403968+00:00
-- url     : https://prove2.me/theorems/48ee29d5-4bbd-4250-9ebe-9bfa1cb707aa
-- title:
--   Match Not Im: emb Hom last row
-- statement:
--   The Match Not Im construction uses the emb Hom last row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasis.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasis.lean#L25-L31

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

theorem GlobalTheory.JR.Step.MatchNotIm.embHom_last_row (g : Matrix (Fin r) (Fin r) k) (j : Fin (r + 1)) :
    embHom r k g (Fin.last r) j = if j = Fin.last r then 1 else 0 := by sorry
