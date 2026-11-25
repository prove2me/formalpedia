-- Prove2me | Theorems.Thm_GlobalTheory_HomExtension_finite_torsion_images
-- name    : GlobalTheory.HomExtension.finite_torsion_images
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:36.868351+00:00
-- url     : https://prove2.me/theorems/42587be9-8757-498b-9dbd-27740da89645
-- title:
--   Hom Extension: finite torsion images
-- statement:
--   The Hom Extension construction uses the finite torsion images property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldIntegralClosurePadicInt.lean#L22-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteResidueFieldIntegralClosurePadicInt.lean#L22-L65

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
open GlobalTheory.HomExtension

theorem GlobalTheory.HomExtension.finite_torsion_images
    (hab : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
      ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1})
    {Z : Scheme.{0}} (G : Over Z) [GrpObj G] (hG : IsSemiAbelian G) (z : Z) {n : ℕ} (hn : 1 ≤ n) :
    {w : G.left | G.hom w = z ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k) (t : Sp k ⟶ Z)
      (x : Over.mk t ⟶ G), x ^ n = 1 ∧ w ∈ Set.range x.left}.Finite := by sorry
