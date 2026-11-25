-- Prove2me | Theorems.Thm_GlobalTheory_regular_of_bounded_at_padicAlgCl_points
-- name    : GlobalTheory.regular_of_bounded_at_padicAlgCl_points
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:29.812848+00:00
-- url     : https://prove2.me/theorems/148cdbb3-234a-464c-8628-ffcaf88b7bee
-- title:
--   Global Theory: regular of bounded at padic Alg Cl points
-- statement:
--   The Global Theory construction uses the regular of bounded at padic Alg Cl points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/RegularOfBoundedAtPadicAlgClPoints.lean#L82-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/RegularOfBoundedAtPadicAlgClPoints.lean#L82-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
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
open BoundedRegular

theorem GlobalTheory.regular_of_bounded_at_padicAlgCl_points :
    (∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (x : X),
      IsClosed ({x} : Set X) → IsIntegrallyClosed (X.presheaf.stalk x) →
      ∀ (U : X.Opens) (φ : Γ(X, U)), (U : Set X).Nonempty →
      (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) = x →
        Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ ≤ 1) →
      ∃ (W : X.Opens) (ψ : Γ(X, W)), x ∈ W ∧
        resG X (inf_le_left : W ⊓ U ≤ W) ψ = resG X (inf_le_right : W ⊓ U ≤ U) φ) ∧
    (∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (U W : X.Opens) (h : U ≤ W) (φ : Γ(X, U)),
      (U : Set X).Nonempty →
      ((∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) ∈ W →
        Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ ≤ 1) →
          ∃! ψ : Γ(X, W), resG X h ψ = φ) ∧
      (IsUnit φ → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) ∈ W →
        Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ = 1) →
          ∃ ψ : Γ(X, W), IsUnit ψ ∧ resG X h ψ = φ)) := by sorry
