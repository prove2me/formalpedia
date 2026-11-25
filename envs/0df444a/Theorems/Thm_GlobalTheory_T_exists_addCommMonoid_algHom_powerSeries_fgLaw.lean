-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_addCommMonoid_algHom_powerSeries_fgLaw
-- name    : GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T18:01:28.110359+00:00
-- url     : https://prove2.me/theorems/d784ef81-38d2-50a7-b4c5-7d5e41659b03
-- title:
--   T: exists add Comm Monoid alg Hom power Series fg Law
-- statement:
--   The T construction uses the exists add Comm Monoid alg Hom power Series fg Law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsAddCommMonoidStatement.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PointsAddCommMonoidStatement.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsAddCommMonoid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsAddCommMonoidStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst; (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧ (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧ ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by sorry
