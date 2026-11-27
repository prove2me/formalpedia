-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_normalizationLift
-- name    : GlobalTheory.existsUnique_normalizationLift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:44:43.375479+00:00
-- url     : https://prove2.me/theorems/30d615da-5a23-4b32-852b-d9abc45a1e79
-- title:
--   Global Theory: exists Unique normalization Lift
-- statement:
--   The Global Theory construction uses the exists Unique normalization Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L66-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {X Y T Z : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
variable (a : X ⟶ T) (g : T ⟶ Z) [IsIntegralHom g] (b : Y ⟶ Z) (H : a ≫ g = f ≫ b)
include H

theorem GlobalTheory.existsUnique_normalizationLift :
    ∃! m : f.normalization ⟶ T, f.toNormalization ≫ m = a ∧ m ≫ g = f.fromNormalization ≫ b := by sorry
