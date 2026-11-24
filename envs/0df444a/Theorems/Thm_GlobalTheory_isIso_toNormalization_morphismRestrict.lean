-- Prove2me | Theorems.Thm_GlobalTheory_isIso_toNormalization_morphismRestrict
-- name    : GlobalTheory.isIso_toNormalization_morphismRestrict
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:46.104831+00:00
-- url     : https://prove2.me/theorems/5de4e8a5-9838-4dc8-b364-0c9857c46eb1
-- title:
--   Global Theory: is Iso to Normalization morphism Restrict
-- statement:
--   The Global Theory construction uses the is Iso to Normalization morphism Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L519-L536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L519-L536

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

theorem GlobalTheory.isIso_toNormalization_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (V : Y.Opens) [IsIntegralHom (f ∣_ V)] :
    IsIso (f.toNormalization ∣_ (f.fromNormalization ⁻¹ᵁ V)) := by sorry
