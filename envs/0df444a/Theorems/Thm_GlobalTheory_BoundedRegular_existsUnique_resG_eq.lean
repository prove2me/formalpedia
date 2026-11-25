-- Prove2me | Theorems.Thm_GlobalTheory_BoundedRegular_existsUnique_resG_eq
-- name    : GlobalTheory.BoundedRegular.existsUnique_resG_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:10:23.898238+00:00
-- url     : https://prove2.me/theorems/2e5e8daa-d14b-587b-93f9-c78b920bfe10
-- title:
--   Bounded Regular: exists Unique res G eq
-- statement:
--   The Bounded Regular construction uses the exists Unique res G eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/RegularOfBoundedAtPadicAlgClPoints.lean#L61-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/RegularOfBoundedAtPadicAlgClPoints.lean#L61-L76

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
open GlobalTheory.BoundedRegular

theorem GlobalTheory.BoundedRegular.existsUnique_resG_eq {X : Scheme.{0}} [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π]
    [LocallyOfFiniteType π] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) {U W : X.Opens}
    (h : U ≤ W) (φ : Γ(X, U)) (hU : (U : Set X).Nonempty)
    (H : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X), y (cPt p) ∈ W →
      Set.range (gPt p ≫ y) ⊆ U → ‖valF (gPt p ≫ y) U φ‖ ≤ 1) :
    ∃! ψ : Γ(X, W), resG X h ψ = φ := by sorry
