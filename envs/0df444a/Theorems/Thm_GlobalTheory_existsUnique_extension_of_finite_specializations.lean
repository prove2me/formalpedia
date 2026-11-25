-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_extension_of_finite_specializations
-- name    : GlobalTheory.existsUnique_extension_of_finite_specializations
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:56:56.344687+00:00
-- url     : https://prove2.me/theorems/3e5335b3-21eb-4fdd-842f-746d2b01775a
-- title:
--   Global Theory: exists Unique extension of finite specializations
-- statement:
--   The Global Theory construction uses the exists Unique extension of finite specializations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteOfIsClosedOfFiniteInterClosedPoints.lean#L62-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteOfIsClosedOfFiniteInterClosedPoints.lean#L62-L122

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
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

theorem GlobalTheory.existsUnique_extension_of_finite_specializations :
    ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π], IsNormalScheme X → ∀ (Z P : Scheme.{0}) (s : X ⟶ Z) (t : P ⟶ Z) [IsProper t] (G : P.Opens) (U : X.Opens) (φ : U.toScheme ⟶ P), (U : Set X).Nonempty → φ ≫ t = U.ι ≫ s → (∀ σ : X, IsClosed ({σ} : Set X) → ∃ F : Set P, F.Finite ∧ F ⊆ G ∧ ∀ (p : ℕ) [Fact p.Prime] (a : Sp (OO p) ⟶ X) (a₀ : Sp (PadicAlgCl p) ⟶ U.toScheme) (b : Sp (OO p) ⟶ P), a (cPt p) = σ → a₀ ≫ U.ι = gPt p ≫ a → gPt p ≫ b = a₀ ≫ φ → b ≫ t = a ≫ s → b (cPt p) ∈ F) → ∃! Φ : X ⟶ G.toScheme, U.ι ≫ Φ ≫ G.ι = φ ∧ Φ ≫ G.ι ≫ t = s := by sorry
