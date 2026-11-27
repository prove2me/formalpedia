-- Prove2me | Theorems.Thm_GlobalTheory_bijective_restrictPoints_of_etale
-- name    : GlobalTheory.bijective_restrictPoints_of_etale
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:23.805414+00:00
-- url     : https://prove2.me/theorems/c84fbef9-6a2e-44e3-b96c-8d56160ac6da
-- title:
--   Global Theory: bijective restrict Points of etale
-- statement:
--   The Global Theory construction uses the bijective restrict Points of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L355-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean#L355-L358

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

theorem GlobalTheory.bijective_restrictPoints_of_etale {X S T₀ T : Scheme.{u}} (f : X ⟶ S) [Etale f]
    (h : T ⟶ S) (i : T₀ ⟶ T) [IsClosedImmersion i] (hi : IsNilpotent i.ker) :
    Function.Bijective (restrictPoints f h i) := by sorry
