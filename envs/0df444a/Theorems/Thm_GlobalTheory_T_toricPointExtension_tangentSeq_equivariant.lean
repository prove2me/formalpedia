-- Prove2me | Theorems.Thm_GlobalTheory_T_toricPointExtension_tangentSeq_equivariant
-- name    : GlobalTheory.T.toricPointExtension_tangentSeq_equivariant
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:31.184856+00:00
-- url     : https://prove2.me/theorems/bed82ed9-a6fa-5492-9691-df56b6f4eed7
-- title:
--   T: toric Point Extension tangent Seq equivariant
-- statement:
--   The T construction uses the toric Point Extension tangent Seq equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ToricPointExtensionTangentSeqEquivariantStatement.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ToricPointExtensionTangentSeqEquivariantStatement.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ToricPointExtensionTangentSeqEquivariant
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ToricPointExtensionTangentSeqEquivariantStatement
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

theorem GlobalTheory.T.toricPointExtension_tangentSeq_equivariant : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → ∀ (f : G ⟶ G) (α : Fin d → PS R 1 d), Reads x x f α → (∀ (fB : B ⟶ B) (αB : Fin g → PS R 1 g), Reads xB xB fB αB → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) z, E.q S h (z ≫ f) = E.q S h z ≫ fB) → lin Q * lin α = lin αB * lin Q) ∧ ∀ hm : X →+ X, (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) χ χ', (∀ y, χ' (Multiplicative.ofAdd y) = χ (Multiplicative.ofAdd (hm y))) → E.i S h χ ≫ f = E.i S h χ') → lin α * lin J = lin J * Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) := by sorry
