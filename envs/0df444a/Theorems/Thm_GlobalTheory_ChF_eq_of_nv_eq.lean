-- Prove2me | Theorems.Thm_GlobalTheory_ChF_eq_of_nv_eq
-- name    : GlobalTheory.ChF.eq_of_nv_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:00.764416+00:00
-- url     : https://prove2.me/theorems/fb6d91e2-847f-58ae-9d2f-5a4dbe82c1a2
-- title:
--   Ch F: eq of nv eq
-- statement:
--   The Ch F construction uses the eq of nv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSeriesEqOfEvalAtNilpotentPointsEq.lean#L50-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSeriesEqOfEvalAtNilpotentPointsEq.lean#L50-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteTorsOfFiniteTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSeriesEqOfEvalAtNilpotentPointsEq
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

theorem GlobalTheory.ChF.eq_of_nv_eq : ∀ (R : Type) [CommRing R] (I : Ideal R), IsHausdorff I R → ∀ (n d : ℕ) (f f' : PS R n d), (∀ (S : Type) [CommRing S] [Algebra R S] (k : ℕ), Kills I k S → (IsLocalRing R → I ≠ ⊤ → IsLocalRing S ∧ IsLocalHom (algebraMap R S)) → ∀ a : Fin n → Fin d → S, (∀ i j, IsNilpotent (a i j)) → nv (algebraMap R S) f a = nv (algebraMap R S) f' a) → f = f' := by sorry
