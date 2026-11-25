-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isFinite_of_unique_lift_of_classical_points
-- name    : GlobalTheory.isIso_of_isFinite_of_unique_lift_of_classical_points
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:14.745926+00:00
-- url     : https://prove2.me/theorems/e220a68e-bec6-4312-bd17-78ea8883a753
-- title:
--   Global Theory: is Iso of is Finite of unique lift of classical points
-- statement:
--   The Global Theory construction uses the is Iso of is Finite of unique lift of classical points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints.lean#L160-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints.lean#L160-L257

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
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

theorem GlobalTheory.isIso_of_isFinite_of_unique_lift_of_classical_points :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π],
      IsNormalScheme X → ∀ (W : Scheme.{0}) [IsReduced W] [Nonempty W] (f : W ⟶ X) [IsFinite f],
        (∀ w ∈ genericPoints W, f w = genericPoint X) → ∀ (x : X) (U : X.Opens),
          IsClosed ({x} : Set X) → (U : Set X).Nonempty →
            (∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ f = a' ≫ f →
              (a ≫ f) (cPt p) = x → Set.range (gPt p ≫ a ≫ f) ⊆ U → a = a') → IsIso f := by sorry
