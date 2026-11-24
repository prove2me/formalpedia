-- Prove2me | Theorems.Thm_GlobalTheory_SiegelAction_sub_conj_eq
-- name    : GlobalTheory.SiegelAction.sub_conj_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:11:40.969527+00:00
-- url     : https://prove2.me/theorems/82342f6f-1f42-4aa3-b29a-4048f661bbcb
-- title:
--   Siegel Action: sub conj eq
-- statement:
--   The Siegel Action construction uses the sub conj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticSiegelActionMemUpperHalfSpaceAndCocycl.lean#L58-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.SiegelAction.sub_conj_eq (τ : Matrix ι ι ℂ) :
    τ - τ.map conj = (2 * I) • τ.map (fun z => (z.im : ℂ)) := by sorry
