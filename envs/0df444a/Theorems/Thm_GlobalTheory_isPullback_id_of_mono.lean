-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_id_of_mono
-- name    : GlobalTheory.isPullback_id_of_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:31:48.852441+00:00
-- url     : https://prove2.me/theorems/542fe076-874f-49b5-8a28-a317050c285b
-- title:
--   Global Theory: is Pullback id of mono
-- statement:
--   The Global Theory construction uses the is Pullback id of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L417-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L417-L418

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
attribute [instance] PreservesNormalization.isIso_normalizationPullback
variable {X Y V : Scheme.{u}} (f' : X ⟶ V) (b : V ⟶ Y) [Mono b] (f : X ⟶ Y) (H : f = f' ≫ b)
include H

theorem GlobalTheory.isPullback_id_of_mono : IsPullback (𝟙 X) f' f b := by sorry
