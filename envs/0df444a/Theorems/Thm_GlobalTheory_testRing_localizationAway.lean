-- Prove2me | Theorems.Thm_GlobalTheory_testRing_localizationAway
-- name    : GlobalTheory.testRing_localizationAway
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:46.786295+00:00
-- url     : https://prove2.me/theorems/65c044be-43e4-5013-89a2-f72389bbf06a
-- title:
--   Global Theory: test Ring localization Away
-- statement:
--   The Global Theory construction uses the test Ring localization Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TestRingLocalizationAway.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TestRingLocalizationAway.lean#L12-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ReducedFiniteTypeIffTestRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TestRingLocalizationAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory

theorem GlobalTheory.testRing_localizationAway :
    ∀ (K : Type) [Field K] (p : TRing K) (g : p.R), ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R), IsUnit (lam g) ∧ ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T), IsUnit (ψ g) → ∃ k : p'.R →ₐ[K] T, k.comp lam = ψ := by sorry
