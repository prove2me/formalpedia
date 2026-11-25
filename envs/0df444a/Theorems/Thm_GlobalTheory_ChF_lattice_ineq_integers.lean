-- Prove2me | Theorems.Thm_GlobalTheory_ChF_lattice_ineq_integers
-- name    : GlobalTheory.ChF.lattice_ineq_integers
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:14.311466+00:00
-- url     : https://prove2.me/theorems/39a7b5d3-66c3-4ade-886d-efdd2fdf7d6a
-- title:
--   Ch F: lattice ineq integers
-- statement:
--   The Ch F construction uses the lattice ineq integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LatticeInequalityValuationIntegers.lean#L226-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LatticeInequalityValuationIntegers.lean#L226-L342

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
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LatticeInequalityValuationIntegers
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

theorem GlobalTheory.ChF.lattice_ineq_integers : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∃ c : C, 0 < v c ∧ v c < 1) → ∀ (n s h : ℕ) (a : Fin n → O), Function.Injective a → ∀ (M : Submodule O (Fin n × Fin s → O)), M.FG → (∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 * f y) ∈ M) → (∀ (τ : Fin n) (z : Fin s → O), ∃ f ∈ M, ∀ i, f (τ, i) = z i) → ∀ (φ : Fin h → Fin n × Fin s → O), (∀ l, φ l ∈ M) → ∀ c : NNReal, c ≠ 0 → HasLen v O (M ⧸ (Submodule.span O (Set.range fun q : Fin n × Fin h => fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y)).comap M.subtype) c → ∃ x : Fin n → NNReal, (∀ τ, HasLen v O ((Fin s → O) ⧸ Submodule.span O (Set.range fun l => fun i => φ l (τ, i))) (x τ)) ∧ c ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ h ≤ (∏ τ, x τ) ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ s := by sorry
