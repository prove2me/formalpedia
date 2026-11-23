-- Prove2me | Theorems.Thm_GlobalTheory_FormalLog_pderiv_logOf
-- name    : GlobalTheory.FormalLog.pderiv_logOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:47.101797+00:00
-- url     : https://prove2.me/theorems/0cc6ca9c-5de0-490b-886e-db90fa9fc09e
-- title:
--   Formal Log: pderiv log Of
-- statement:
--   The Formal Log construction uses the pderiv log Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PderivSecondEvFirstPointEqZero.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PderivSecondEvFirstPointEqZero.lean#L59-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
variable [Algebra ℚ k]

theorem GlobalTheory.FormalLog.pderiv_logOf (i a : Fin d) : pderiv k ((0 : Fin 1), a) (logOf G i) = Om G i a := by sorry
