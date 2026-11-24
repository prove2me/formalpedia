-- Prove2me | Theorems.Thm_GlobalTheory_SW_HAct_det_re
-- name    : GlobalTheory.SW.HAct.det_re
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:40:47.141895+00:00
-- url     : https://prove2.me/theorems/3b6a1cf1-7b18-40e0-8001-72a3e510f620
-- title:
--   HAct: det re
-- statement:
--   The HAct construction uses the det re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/UnitaryActHalfSpace.lean#L103-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}

theorem GlobalTheory.SW.HAct.det_re {Q Y X : Matrix (Fin N) (Fin N) ℂ} (h : Qᴴ * Y * Q = X) :
    Y.det.re * ‖Q.det‖ ^ 2 = X.det.re := by sorry
