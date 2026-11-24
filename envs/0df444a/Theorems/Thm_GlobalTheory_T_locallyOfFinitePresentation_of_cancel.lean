-- Prove2me | Theorems.Thm_GlobalTheory_T_locallyOfFinitePresentation_of_cancel
-- name    : GlobalTheory.T.locallyOfFinitePresentation_of_cancel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:17.071818+00:00
-- url     : https://prove2.me/theorems/c5e5ec18-cb9c-4447-aeee-f9f9bbe8fb04
-- title:
--   T: locally Of Finite Presentation of cancel
-- statement:
--   The T construction uses the locally Of Finite Presentation of cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/LocallyOfFinitePresentationOfCancelStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/LocallyOfFinitePresentationOfCancelStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_LocallyOfFinitePresentationOfCancel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_LocallyOfFinitePresentationOfCancelStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.locallyOfFinitePresentation_of_cancel : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q → LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) → LocallyOfFinitePresentation f := by sorry
