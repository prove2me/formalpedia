-- Prove2me | Theorems.Thm_GlobalTheory_FormalChartOf_tmul_eps_eq_zero
-- name    : GlobalTheory.FormalChartOf.tmul_eps_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:45:32.773848+00:00
-- url     : https://prove2.me/theorems/d1274995-31aa-4aff-a75a-510b6fdb2a09
-- title:
--   Formal Chart Of: tmul eps eq zero
-- statement:
--   The Formal Chart Of construction uses the tmul eps eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalChart.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsFormalChart.lean#L75-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FormalChartOf
variable {R₀ : Type} [CommRing R₀]

theorem GlobalTheory.FormalChartOf.tmul_eps_eq_zero [IsLocalRing R₀] {M : Type} [AddCommGroup M] [Module R₀ M]
    (w : M) (h : w ⊗ₜ[R₀] epsK R₀ = 0) : w = 0 := by sorry
