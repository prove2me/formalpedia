-- Prove2me | Theorems.Thm_GlobalTheory_MulJacobian_isUnit_det_of_const
-- name    : GlobalTheory.MulJacobian.isUnit_det_of_const
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:28:50.149058+00:00
-- url     : https://prove2.me/theorems/62947ba5-a051-40cc-a03a-4fb010438d26
-- title:
--   Mul Jacobian: is Unit det of const
-- statement:
--   The Mul Jacobian construction uses the is Unit det of const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/DetJacobianFormalMulNEqPowMulUnit.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/DetJacobianFormalMulNEqPowMulUnit.lean#L31-L38

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

theorem GlobalTheory.MulJacobian.isUnit_det_of_const {σ : Type} (M : Matrix (Fin d) (Fin d) (MvPowerSeries σ R))
    (h : ∀ j i, constantCoeff (M j i) = (1 : Matrix (Fin d) (Fin d) R) j i) : IsUnit M.det := by sorry
