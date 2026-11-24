-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCoverGrowth_separable_map
-- name    : GlobalTheory.FiniteCoverGrowth.separable_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:45.00579+00:00
-- url     : https://prove2.me/theorems/eaca79e0-8eff-463a-a89b-d95f563f1ec8
-- title:
--   Finite Cover Growth: separable map
-- statement:
--   The Finite Cover Growth construction uses the separable map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IntegralAndRationalOfPolynomialGrowth.lean#L121-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IntegralAndRationalOfPolynomialGrowth.lean#L121-L131

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

theorem GlobalTheory.FiniteCoverGrowth.separable_map {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q : MvPolynomial (Fin d) ℂ) (hq : Polynomial.C q ∈ Ideal.span {p, p.derivative})
    (x : Fin d → ℂ) (hx : MvPolynomial.eval x q ≠ 0) :
    (p.map (MvPolynomial.eval x)).Separable := by sorry
