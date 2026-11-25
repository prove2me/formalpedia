-- Prove2me | Theorems.Thm_GlobalTheory_BoundedRegular_valF_spMap_comp_eq
-- name    : GlobalTheory.BoundedRegular.valF_spMap_comp_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:13:31.128928+00:00
-- url     : https://prove2.me/theorems/395fea96-cad0-4299-a489-bc61630eb041
-- title:
--   Bounded Regular: val F sp Map comp eq
-- statement:
--   The Bounded Regular construction uses the val F sp Map comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/RegularOfBoundedAtPadicAlgClPoints.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/RegularOfBoundedAtPadicAlgClPoints.lean#L17-L28

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

theorem GlobalTheory.BoundedRegular.valF_spMap_comp_eq {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}}
    (t : Sp F ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) (φ : Γ(X, U)) :
    valF (spMap f ≫ t) U φ =
      f ((Scheme.ΓSpecIso (CommRingCat.of F)).hom (t.appLE U ⊤ ht φ)) := by sorry
