-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LfpDescent_descends
-- name    : GlobalTheory.CompanionTheory.LfpDescent.descends
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:52:14.241686+00:00
-- url     : https://prove2.me/theorems/417138ee-622e-4a69-afdc-4368fd116f11
-- title:
--   Lfp Descent: descends
-- statement:
--   The Lfp Descent construction uses the descends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/LocallyOfFinitePresentationOfCancel.lean#L34-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/LocallyOfFinitePresentationOfCancel.lean#L34-L59

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FinitePresentationOfFaithfullyFlatStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_LocallyOfFinitePresentationOfCancel
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_FiniteTypeDescent_main__3dbb7f300c14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LfpDescent

theorem GlobalTheory.CompanionTheory.LfpDescent.descends : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q →
    LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) →
    LocallyOfFinitePresentation f := by sorry
