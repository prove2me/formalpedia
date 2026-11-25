-- Prove2me | Theorems.Thm_GlobalTheory_exists_affineOpen_factor_of_isLocalRing
-- name    : GlobalTheory.exists_affineOpen_factor_of_isLocalRing
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:49.176307+00:00
-- url     : https://prove2.me/theorems/a13d34a0-ca48-5258-a92f-d94b35a02e32
-- title:
--   Global Theory: exists affine Open factor of is Local Ring
-- statement:
--   The Global Theory construction uses the exists affine Open factor of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemPadicAlgClValuationSubringIffNormLeOne.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemPadicAlgClValuationSubringIffNormLeOne.lean#L79-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
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
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.exists_affineOpen_factor_of_isLocalRing {R : CommRingCat.{0}} [IsLocalRing R]
    {X : Scheme.{0}} (y : Spec R ⟶ X) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (φ : Γ(X, V) ⟶ R), Spec.map φ ≫ hV.fromSpec = y := by sorry
