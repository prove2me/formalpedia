-- Prove2me | Theorems.Thm_GlobalTheory_flat_normalization_of_isBezout
-- name    : GlobalTheory.flat_normalization_of_isBezout
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:47.46655+00:00
-- url     : https://prove2.me/theorems/9a59ae01-c145-57e3-b40a-37cec657c9f9
-- title:
--   Global Theory: flat normalization of is Bezout
-- statement:
--   The Global Theory construction uses the flat normalization of is Bezout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L587-L590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoNormalizationPullbackOfToIntegralClosure.lean#L587-L590

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  {R : Type u} [CommRing R]

theorem GlobalTheory.flat_normalization_of_isBezout [IsDomain R] [IsBezout R]
    (p : f.normalization ⟶ Spec (.of R)) [Flat (f.toNormalization ≫ p)] : Flat p := by sorry
