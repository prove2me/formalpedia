-- Prove2me | Theorems.Thm_GlobalTheory_T_det_jacobian_formalMulN_eq_pow_mul_unit
-- name    : GlobalTheory.T.det_jacobian_formalMulN_eq_pow_mul_unit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:29:56.280853+00:00
-- url     : https://prove2.me/theorems/27a4c90d-bc96-4db8-8271-62221438bc0f
-- title:
--   T: det jacobian formal Mul N eq pow mul unit
-- statement:
--   The T construction uses the det jacobian formal Mul N eq pow mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/DetJacobianFormalMulNEqPowMulUnitStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/DetJacobianFormalMulNEqPowMulUnitStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnit
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DetJacobianFormalMulNEqPowMulUnitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.det_jacobian_formalMulN_eq_pow_mul_unit : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (N : ℕ), ∃ U : (PS R 1 d)ˣ, Matrix.det (Matrix.of fun i j : Fin d => MvPowerSeries.pderiv R ((0 : Fin 1), j) (mulF F.F N i)) = (N : PS R 1 d) ^ d * U := by sorry
