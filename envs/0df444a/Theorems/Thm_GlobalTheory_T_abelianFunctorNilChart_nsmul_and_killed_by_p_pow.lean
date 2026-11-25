-- Prove2me | Theorems.Thm_GlobalTheory_T_abelianFunctorNilChart_nsmul_and_killed_by_p_pow
-- name    : GlobalTheory.T.abelianFunctorNilChart_nsmul_and_killed_by_p_pow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T18:31:34.312605+00:00
-- url     : https://prove2.me/theorems/3bff97af-89fe-4f1e-b84e-a72175840446
-- title:
--   T: abelian Functor Nil Chart nsmul and killed by p pow
-- statement:
--   The T construction uses the abelian Functor Nil Chart nsmul and killed by p pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AbelianFunctorNilChartNsmulAndKilledByPPowStatement.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AbelianFunctorNilChartNsmulAndKilledByPPowStatement.lean#L20-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AbelianFunctorNilChartNsmulAndKilledByPPow
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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AbelianFunctorNilChartNsmulAndKilledByPPowStatement
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

theorem GlobalTheory.T.abelianFunctorNilChart_nsmul_and_killed_by_p_pow : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (p : ℕ) (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), IsNilpotent (p : (R : Type)) → (∀ i, IsNilpotent (a i)) → (∀ N : ℕ, N • Y R s a = Y R s (fun j => nv s.1.toRingHom (mulF F.F N j) ![a])) ∧ ∃ n : ℕ, p ^ (n + 1) • Y R s a = 0 := by sorry
