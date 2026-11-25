-- Prove2me | Theorems.Thm_GlobalTheory_CoordChart_residue_generic
-- name    : GlobalTheory.CoordChart.residue_generic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:04:43.610364+00:00
-- url     : https://prove2.me/theorems/2112651f-bdd8-4876-b68f-d391b81b40d6
-- title:
--   Coord Chart: residue generic
-- statement:
--   The Coord Chart construction uses the residue generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ResidueGeneric.lean#L88-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ResidueGeneric.lean#L88-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ResidueGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoordChart

theorem GlobalTheory.CoordChart.residue_generic : ∀ (o : Type) [CommRing o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R) (K : Type) [Field K] (y : R →+* K) (a₀ : Ix g (N' ^ 2)), 0 < N' → IsOpenImmersion x → x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → (∀ k : K, ∃ r r' : R, y r' ≠ 0 ∧ k * y r' = y r) → y (v a₀) ≠ 0 → Subfield.closure (Set.range (y.comp β) ∪ Set.range (fun a => y (v a) / y (v a₀))) = ⊤ ∧ (RingHom.ker y ∈ minimalPrimes R → RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) (fun a => y (v a) / y (v a₀))) ∈ (I ⊔ Ideal.span {MvPolynomial.X a₀ - 1}).minimalPrimes) := by sorry
