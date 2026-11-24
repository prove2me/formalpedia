-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCoverGrowth_contDiff_eval_map
-- name    : GlobalTheory.FiniteCoverGrowth.contDiff_eval_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:28.733584+00:00
-- url     : https://prove2.me/theorems/0b16393f-0227-4278-9ee0-2f2fd61133de
-- title:
--   Finite Cover Growth: cont Diff eval map
-- statement:
--   The Finite Cover Growth construction uses the cont Diff eval map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IntegralAndRationalOfPolynomialGrowth.lean#L88-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IntegralAndRationalOfPolynomialGrowth.lean#L88-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth

theorem GlobalTheory.FiniteCoverGrowth.contDiff_eval_map {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) :
    ContDiff ℂ 1 (fun z : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval z.1)).eval z.2) := by sorry
