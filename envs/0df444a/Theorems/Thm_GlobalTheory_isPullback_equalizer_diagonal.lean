-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_equalizer_diagonal
-- name    : GlobalTheory.isPullback_equalizer_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:21.283405+00:00
-- url     : https://prove2.me/theorems/345a509f-7e5f-457b-a2b3-a22a0292b931
-- title:
--   Global Theory: is Pullback equalizer diagonal
-- statement:
--   The Global Theory construction uses the is Pullback equalizer diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L9-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory

theorem GlobalTheory.isPullback_equalizer_diagonal {X S T : Scheme.{u}} (f : X ⟶ S) {a b : T ⟶ X}
    (hab : a ≫ f = b ≫ f) :
    IsPullback (equalizer.ι a b ≫ a) (equalizer.ι a b) (pullback.diagonal f)
      (pullback.lift a b hab) := by sorry
