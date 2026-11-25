-- Prove2me | Theorems.Thm_GlobalTheory_EigAdd_eigDim_add_transpose
-- name    : GlobalTheory.EigAdd.eigDim_add_transpose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:55.336843+00:00
-- url     : https://prove2.me/theorems/bc30916b-3c3c-43d6-8487-06e8839f44cf
-- title:
--   Eig Add: eig Dim add transpose
-- statement:
--   The Eig Add construction uses the eig Dim add transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EigenspaceDimAddSplitExactTranspose.lean#L75-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EigenspaceDimAddSplitExactTranspose.lean#L75-L93

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SquarefreeMapMinpolyInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenspaceDimAddSplitExactTranspose
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
open GlobalTheory GlobalTheory.EigAdd

theorem GlobalTheory.EigAdd.eigDim_add_transpose : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (d r g : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O), SplitEx A B → ∀ (ρ : OE →+* Matrix (Fin d) (Fin d) O) (ρA : OE →+* Matrix (Fin r) (Fin r) O) (ρB : OE →+* Matrix (Fin g) (Fin g) O), (∀ a, B * ρ a = ρB a * B) → (∀ a, ρ a * A = A * ρA a) → ∀ τ : OE →+* C, eigDim C ρ τ = eigDim C ρA τ + eigDim C ρB τ ∧ eigDim C (fun a => (ρ a)ᵀ) τ = eigDim C ρ τ := by sorry
