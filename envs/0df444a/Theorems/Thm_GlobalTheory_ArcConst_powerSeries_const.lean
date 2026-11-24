-- Prove2me | Theorems.Thm_GlobalTheory_ArcConst_powerSeries_const
-- name    : GlobalTheory.ArcConst.powerSeries_const
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:59:36.330421+00:00
-- url     : https://prove2.me/theorems/850751dd-e38a-4666-a06a-a8b2950731c1
-- title:
--   Arc Const: power Series const
-- statement:
--   The Arc Const construction uses the power Series const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L55-L64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst

theorem GlobalTheory.ArcConst.powerSeries_const {K : Type} [Field K] [CharZero K] {p : PowerSeries K} (hp : AlgZ p) :
    ∃ x : K, p = PowerSeries.C (R := K) x := by sorry
