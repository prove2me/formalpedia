-- Prove2me | Theorems.Thm_GlobalTheory_ChF_nv_calculus
-- name    : GlobalTheory.ChF.nv_calculus
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:00:06.705728+00:00
-- url     : https://prove2.me/theorems/e842af8d-fd4a-54e5-bcff-36d4ec8e45ef
-- title:
--   Ch F: nv calculus
-- statement:
--   The Ch F construction uses the nv calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NEvalSqZero.lean#L48-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NEvalSqZero.lean#L48-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteTorsOfFiniteTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
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

theorem GlobalTheory.ChF.nv_calculus : ∀ (R S : Type) [CommRing R] [CommRing S] (s : R →+* S) (n d : ℕ) (a : Fin n → Fin d → S), (∀ i j, IsNilpotent (a i j)) → (∃ ψ : PS R n d →+* S, (∀ f, ψ f = nv s f a) ∧ (∀ c, ψ (MvPowerSeries.C c) = s c) ∧ ∀ q : Fin n × Fin d, ψ (MvPowerSeries.X q) = a q.1 q.2) ∧ (∀ f : PS R n d, MvPowerSeries.constantCoeff f = 0 → IsNilpotent (nv s f a) ∧ nv s f a ∈ Ideal.span (Set.range fun q : Fin n × Fin d => a q.1 q.2)) ∧ (∀ (m e : ℕ) (b : Fin m → Fin e → PS R n d) (f : PS R m e), (∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) → nv s (sub b f) a = nv s f (fun i j => nv s (b i j) a)) ∧ (∀ (R' : Type) [CommRing R'] (β : R' →+* R) (f : PS R' n d), nv (s.comp β) f a = nv s (MvPowerSeries.map β f) a) ∧ (∀ (S' : Type) [CommRing S'] (t : S →+* S') (f : PS R n d), t (nv s f a) = nv (t.comp s) f (fun i j => t (a i j))) ∧ ((∀ i j i' j', a i j * a i' j' = 0) → ∀ f : PS R n d, nv s f a = s (MvPowerSeries.constantCoeff f) + ∑ q : Fin n × Fin d, s (MvPowerSeries.coeff (Finsupp.single q 1) f) * a q.1 q.2) := by sorry
