-- Prove2me | Theorems.Thm_GlobalTheory_eval_mvPolynomialOnLine
-- name    : GlobalTheory.eval_mvPolynomialOnLine
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:19:41.686297+00:00
-- url     : https://prove2.me/theorems/c26f4543-4dbd-4e65-9179-7fde8f0b0370
-- title:
--   Global Theory: eval mv Polynomial On Line
-- statement:
--   The Global Theory construction uses the eval mv Polynomial On Line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedAndDenseComplHypersurface.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedAndDenseComplHypersurface.lean#L15-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedAndDenseComplHypersurface
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
open GlobalTheory

theorem GlobalTheory.eval_mvPolynomialOnLine {d : ℕ} (q : MvPolynomial (Fin d) ℂ) (a b : Fin d → ℂ) (t : ℂ) :
    (mvPolynomialOnLine q a b).eval t = MvPolynomial.eval (a + t • (b - a)) q := by sorry
