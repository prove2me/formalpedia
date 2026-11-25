-- Prove2me | Theorems.Thm_GlobalTheory_ChF_hasLen_exists_mono_fp
-- name    : GlobalTheory.ChF.hasLen_exists_mono_fp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:47.500134+00:00
-- url     : https://prove2.me/theorems/af7b4097-d9d2-4a81-9046-213acd61e0f1
-- title:
--   Ch F: has Len exists mono fp
-- statement:
--   The Ch F construction uses the has Len exists mono fp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/HasLenExistsMonoFp.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/HasLenExistsMonoFp.lean#L91-L94

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
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HasLenExistsMonoFp
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
open GlobalTheory GlobalTheory.ChF

theorem GlobalTheory.ChF.hasLen_exists_mono_fp : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∀ (M : Type) [AddCommGroup M] [Module O M], Module.FinitePresentation O M → ∃ x, HasLen v O M x) ∧ (∀ (M M' : Type) [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M') (x x' : NNReal), Function.Surjective f → HasLen v O M x → HasLen v O M' x' → x ≤ x') ∧ ∀ (n : ℕ) (M N : Submodule O (Fin n → O)), M.FG → N.FG → N ≤ M → Module.FinitePresentation O (M ⧸ N.comap M.subtype) := by sorry
