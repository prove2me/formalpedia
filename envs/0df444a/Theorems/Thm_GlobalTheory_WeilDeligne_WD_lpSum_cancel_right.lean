-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_cancel_right
-- name    : GlobalTheory.WeilDeligne.WD.lpSum_cancel_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:02:25.216277+00:00
-- url     : https://prove2.me/theorems/6e260e5f-c039-5bac-9f49-933c589fc577
-- title:
--   WD: lp Sum cancel right
-- statement:
--   The WD construction uses the lp Sum cancel right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/DirectSumCancelRight.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/DirectSumCancelRight.lean#L8-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismFamilyDirectSummandCancellationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_DirectSumCancelRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.WD

theorem GlobalTheory.WeilDeligne.WD.lpSum_cancel_right : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h), a.lpSum c = b.lpSum c → a = b := by sorry
