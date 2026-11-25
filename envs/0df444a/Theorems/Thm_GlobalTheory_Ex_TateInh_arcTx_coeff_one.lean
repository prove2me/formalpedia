-- Prove2me | Theorems.Thm_GlobalTheory_Ex_TateInh_arcTx_coeff_one
-- name    : GlobalTheory.Ex.TateInh.arcTx_coeff_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:05:19.210415+00:00
-- url     : https://prove2.me/theorems/cbf7da9f-5c5a-478a-a6e1-6d664886173d
-- title:
--   Tate Inh: arc Tx coeff one
-- statement:
--   The Tate Inh construction uses the arc Tx coeff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L506-L521
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L506-L521

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh

theorem GlobalTheory.Ex.TateInh.arcTx_coeff_one :
    PowerSeries.coeff 1 ((tate (1 : ℤˣ)).arcTx (tateBe 1 1 one_ne_zero).be 1 1) = 2 := by sorry
