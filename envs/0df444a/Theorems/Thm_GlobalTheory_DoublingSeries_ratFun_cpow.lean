-- Prove2me | Theorems.Thm_GlobalTheory_DoublingSeries_ratFun_cpow
-- name    : GlobalTheory.DoublingSeries.ratFun_cpow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:13:52.28547+00:00
-- url     : https://prove2.me/theorems/a217ce45-f912-4cb1-9aa4-ea591a4ae04c
-- title:
--   Doubling Series: rat Fun cpow
-- statement:
--   The Doubling Series construction uses the rat Fun cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L14-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RatFunDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
noncomputable section
open GlobalTheory GlobalTheory.DoublingSeries

theorem GlobalTheory.DoublingSeries.ratFun_cpow {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (s : ℂ) :
    lFactor q α (s + 1 / 2) * lFactor q α⁻¹ (s + 1 / 2) * invNormFactor q N s =
      ratFun q N α ((q : ℂ) ^ (-s)) := by sorry
