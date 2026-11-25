-- Prove2me | Theorems.Thm_GlobalTheory_BoundedRegular_exists_point_norm_valF_eq
-- name    : GlobalTheory.BoundedRegular.exists_point_norm_valF_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:59:03.722446+00:00
-- url     : https://prove2.me/theorems/aedddc94-c42d-407b-8965-f6dd2d6719f3
-- title:
--   Bounded Regular: exists point norm val F eq
-- statement:
--   The Bounded Regular construction uses the exists point norm val F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/RegularOfBoundedAtPadicAlgClPoints.lean#L36-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/RegularOfBoundedAtPadicAlgClPoints.lean#L36-L59

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

theorem GlobalTheory.BoundedRegular.exists_point_norm_valF_eq {X : Scheme.{0}} {p : ℕ} [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ X) (U : X.Opens)
    (hy : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y) ⁻¹ᵁ U)
    (φ : Γ(X, U)) :
    ∃ y' : Sp (OO p) ⟶ X, y' (cPt p) = y (IsLocalRing.closedPoint (integralClosure ℤ_[p] K)) ∧
      Set.range (gPt p ≫ y') ⊆ U ∧
      valF (gPt p ≫ y') U φ = (((Scheme.ΓSpecIso (.of K)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y).appLE
          U ⊤ hy φ) : K) : PadicAlgCl p) := by sorry
