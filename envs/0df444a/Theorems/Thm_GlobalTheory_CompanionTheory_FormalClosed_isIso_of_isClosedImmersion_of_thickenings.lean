-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FormalClosed_isIso_of_isClosedImmersion_of_thickenings
-- name    : GlobalTheory.CompanionTheory.FormalClosed.isIso_of_isClosedImmersion_of_thickenings
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:03:54.000829+00:00
-- url     : https://prove2.me/theorems/b8e825be-723d-580e-90ce-0f73619db278
-- title:
--   Formal Closed: is Iso of is Closed Immersion of thickenings
-- statement:
--   The Formal Closed construction uses the is Iso of is Closed Immersion of thickenings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsIsoOfIsClosedImmersionOfThickenings.lean#L55-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsIsoOfIsClosedImmersionOfThickenings.lean#L55-L75

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_FormalAlgebraisation_GEClosedProj
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsIsoOfIsClosedImmersionOfThickenings
import Theorems.Thm_GlobalTheory_isIso_of_isClosedImmersion_of_thickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FormalClosed
open GlobalTheory.ThickeningClosed

theorem GlobalTheory.CompanionTheory.FormalClosed.isIso_of_isClosedImmersion_of_thickenings :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom →
    ∀ (E : Scheme.{0}) (j : E ⟶ X.left), IsClosedImmersion j →
      (∀ e, ∃ h : (thickObj R I e X).left ⟶ E, h ≫ j = pullback.fst X.hom (thick R I e)) →
        IsIso j := by sorry
