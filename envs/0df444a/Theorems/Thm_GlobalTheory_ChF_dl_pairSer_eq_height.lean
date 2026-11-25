-- Prove2me | Theorems.Thm_GlobalTheory_ChF_dl_pairSer_eq_height
-- name    : GlobalTheory.ChF.dl_pairSer_eq_height
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T18:17:48.434258+00:00
-- url     : https://prove2.me/theorems/59748d8a-3253-4e10-8897-6de30de40b82
-- title:
--   Ch F: dl pair Ser eq height
-- statement:
--   The Ch F construction uses the dl pair Ser eq height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LinearPartPairingSeriesEqHeight.lean#L26-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LinearPartPairingSeriesEqHeight.lean#L26-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinearPartPairingSeriesEqHeight
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF

theorem GlobalTheory.ChF.dl_pairSer_eq_height : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (p : ℕ) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) (g : ℕ) (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)), TanMat B Tw.O Y gb S → ∀ (τ : ℕ → B.G Tw.O) (u : PS (Tw.O : Type) 1 g), MvPowerSeries.constantCoeff u = 1 → PairSer B Tw.O Y p τ u → ∀ ht : B.gg →ₗ[R₀] (Tw.O : Type), (∀ n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ n)) ((Tw.q n).1.toLinearMap ∘ₗ ht)) → Sᵀ *ᵥ dl u = fun l => ht (gb l) := by sorry
