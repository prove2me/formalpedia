-- Prove2me | Theorems.Thm_GlobalTheory_exists_opens_etale_of_unique_classical_points
-- name    : GlobalTheory.exists_opens_etale_of_unique_classical_points
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:24:29.196258+00:00
-- url     : https://prove2.me/theorems/f95a4fdb-5974-4112-b8f9-9190a68508ca
-- title:
--   Global Theory: exists opens etale of unique classical points
-- statement:
--   The Global Theory construction uses the exists opens etale of unique classical points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsOpensEtaleOfUniqueClassicalPoints.lean#L216-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsOpensEtaleOfUniqueClassicalPoints.lean#L216-L311

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

theorem GlobalTheory.exists_opens_etale_of_unique_classical_points :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (W : Scheme.{0}) [IsIntegral W] (u : W ⟶ X) [LocallyOfFiniteType u] [IsSeparated u] [IsDominant u] (w : W) (U : W.Opens), IsClosed ({w} : Set W) → u.QuasiFiniteAt w → (U : Set W).Nonempty → (∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W), a ≫ u = a' ≫ u → a (cPt p) = w → spMap (IsLocalRing.residue (OO p)) ≫ a = spMap (IsLocalRing.residue (OO p)) ≫ a' → Set.range (gPt p ≫ a) ⊆ U → Set.range (gPt p ≫ a') ⊆ U → a = a') → ∃ V : W.Opens, w ∈ V ∧ Etale (V.ι ≫ u) := by sorry
