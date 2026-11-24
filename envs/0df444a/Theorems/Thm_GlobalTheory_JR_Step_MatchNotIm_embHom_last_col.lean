-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_MatchNotIm_embHom_last_col
-- name    : GlobalTheory.JR.Step.MatchNotIm.embHom_last_col
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:19.218966+00:00
-- url     : https://prove2.me/theorems/de873a72-2dfd-46dc-bb2f-3efb4fd5f0dc
-- title:
--   Match Not Im: emb Hom last col
-- statement:
--   The Match Not Im construction uses the emb Hom last col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasis.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasis.lean#L33-L39

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

theorem GlobalTheory.JR.Step.MatchNotIm.embHom_last_col (g : Matrix (Fin r) (Fin r) k) (i : Fin (r + 1)) :
    embHom r k g i (Fin.last r) = if i = Fin.last r then 1 else 0 := by sorry
