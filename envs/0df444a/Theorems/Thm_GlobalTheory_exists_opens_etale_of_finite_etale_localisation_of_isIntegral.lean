-- Prove2me | Theorems.Thm_GlobalTheory_exists_opens_etale_of_finite_etale_localisation_of_isIntegral
-- name    : GlobalTheory.exists_opens_etale_of_finite_etale_localisation_of_isIntegral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:23:22.445172+00:00
-- url     : https://prove2.me/theorems/2edaed0f-1e46-4e08-9b7d-3a92de63942e
-- title:
--   Global Theory: exists opens etale of finite etale localisation of is Integral
-- statement:
--   The Global Theory construction uses the exists opens etale of finite etale localisation of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsOpensEtaleOfUniqueClassicalPoints.lean#L95-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsOpensEtaleOfUniqueClassicalPoints.lean#L95-L175

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsOpensEtaleOfUniqueClassicalPoints
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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory

theorem GlobalTheory.exists_opens_etale_of_finite_etale_localisation_of_isIntegral
    (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π]
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (W : Scheme.{0}) [IsIntegral W] (u : W ⟶ X)
    [LocallyOfFiniteType u] [IsDominant u] (w : W) (U : W.Opens) (hw : IsClosed ({w} : Set W))
    (hU : (U : Set W).Nonempty)
    (huniq : ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ u = a' ≫ u → a (cPt p) = w →
      spMap (IsLocalRing.residue (OO p)) ≫ a = spMap (IsLocalRing.residue (OO p)) ≫ a' →
        Set.range (gPt p ≫ a) ⊆ U → Set.range (gPt p ≫ a') ⊆ U → a = a')
    {T V : Scheme.{0}} [IsIntegral T] (g : T ⟶ X) [Etale g] (h : V ⟶ W) [Etale h] (f : V ⟶ T)
    [IsFinite f] (sq : h ≫ u = f ≫ g)
    (hmono : ∀ (Z : Scheme.{0}) (a b : Z ⟶ V), a ≫ h = b ≫ h → a ≫ f = b ≫ f → a = b)
    (v : V) (hv : h v = w)
    (hgeo : ∀ (K : Type) [Field K] (a b : Spec (.of K) ⟶ V), a ≫ f = b ≫ f →
      (a ≫ f) (IsLocalRing.closedPoint K) = f v →
        a ≫ h = b ≫ h ∧ (a ≫ h) (IsLocalRing.closedPoint K) = w) :
    ∃ V : W.Opens, w ∈ V ∧ Etale (V.ι ≫ u) := by sorry
