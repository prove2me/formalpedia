-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_hom_extension_semiAbelian_normal_base
-- name    : GlobalTheory.existsUnique_hom_extension_semiAbelian_normal_base
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:18:16.093799+00:00
-- url     : https://prove2.me/theorems/a6b74fbc-6fcb-407d-80b3-f334382b6dd9
-- title:
--   Global Theory: exists Unique hom extension semi Abelian normal base
-- statement:
--   The Global Theory construction uses the exists Unique hom extension semi Abelian normal base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldIntegralClosurePadicInt.lean#L209-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldIntegralClosurePadicInt.lean#L209-L267

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulEquivOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldIntegralClosurePadicInt
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
open HomExtension

theorem GlobalTheory.existsUnique_hom_extension_semiAbelian_normal_base : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → ∀ (Z : Scheme.{0}) [IsIntegral Z] (π : Z ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (G G' P' : Over Z) [GrpObj G] [GrpObj G'] (κ : G' ⟶ P'), IsSemiAbelian G → IsSemiAbelian G' → IsProper P'.hom → IsOpenImmersion κ.left → ∀ (U : Z.Opens), (U : Set Z).Nonempty → ∀ φ : (Over.pullback U.ι).obj G ⟶ (Over.pullback U.ι).obj G', IsMonHom φ → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback U.ι).map F = φ := by sorry
