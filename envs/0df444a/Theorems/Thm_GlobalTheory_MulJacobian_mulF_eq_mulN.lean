-- Prove2me | Theorems.Thm_GlobalTheory_MulJacobian_mulF_eq_mulN
-- name    : GlobalTheory.MulJacobian.mulF_eq_mulN
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:23.410432+00:00
-- url     : https://prove2.me/theorems/8eac2560-b500-416b-bcc5-69c4dc342f6a
-- title:
--   Mul Jacobian: mul F eq mul N
-- statement:
--   The Mul Jacobian construction uses the mul F eq mul N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/DetJacobianFormalMulNEqPowMulUnit.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/DetJacobianFormalMulNEqPowMulUnit.lean#L18-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LawRightUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnit
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open GlobalTheory GlobalTheory.MulJacobian
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.MulJacobian.mulF_eq_mulN (G : FGLaw R d) (N : ℕ) : mulF G.F N = mulN G N := by sorry
