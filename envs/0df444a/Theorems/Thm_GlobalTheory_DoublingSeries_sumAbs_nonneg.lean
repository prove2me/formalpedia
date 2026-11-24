-- Prove2me | Theorems.Thm_GlobalTheory_DoublingSeries_sumAbs_nonneg
-- name    : GlobalTheory.DoublingSeries.sumAbs_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:13:47.350601+00:00
-- url     : https://prove2.me/theorems/36fe9e9a-3128-417b-88f7-9db6c306f651
-- title:
--   Doubling Series: sum Abs nonneg
-- statement:
--   The Doubling Series construction uses the sum Abs nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RatFunDifferentiableOn.lean#L83-L84

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

theorem GlobalTheory.DoublingSeries.sumAbs_nonneg {D : Type} [Fintype D] (e : D → ℤ) : 0 ≤ sumAbs e := by sorry
