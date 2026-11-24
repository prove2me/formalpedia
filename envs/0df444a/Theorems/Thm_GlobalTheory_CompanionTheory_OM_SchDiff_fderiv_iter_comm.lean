-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OM_SchDiff_fderiv_iter_comm
-- name    : GlobalTheory.CompanionTheory.OM.SchDiff.fderiv_iter_comm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:53:30.18088+00:00
-- url     : https://prove2.me/theorems/11e5424c-0801-44f4-bf8f-d5ca7b7fabdb
-- title:
--   Sch Diff: fderiv iter comm
-- statement:
--   The Sch Diff construction uses the fderiv iter comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoundMulTranslate.lean#L16-L36

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_ExistsHarrisTaylorObjectOfLevelLift
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoundMulTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OM GlobalTheory.CompanionTheory.OM.SchDiff
variable {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.CompanionTheory.OM.SchDiff.fderiv_iter_comm {F : X → V} (hF : ContDiff ℝ ∞ F) (h : X) (n : ℕ) (a : X) :
    fderiv ℝ (iteratedFDeriv ℝ n F) a h = iteratedFDeriv ℝ n (fun b => fderiv ℝ F b h) a := by sorry
