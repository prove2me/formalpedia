-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_exists_local_log
-- name    : GlobalTheory.SmoothForms.exists_local_log
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:09.758311+00:00
-- url     : https://prove2.me/theorems/936899ea-8e12-4e53-965c-936bdcc98be3
-- title:
--   Smooth Forms: exists local log
-- statement:
--   The Smooth Forms construction uses the exists local log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HasSmoothLogNearOneOfIsUnitaryLieExpData.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/HasSmoothLogNearOneOfIsUnitaryLieExpData.lean#L24-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HasSmoothLogNearOneOfIsUnitaryLieExpData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms

theorem GlobalTheory.SmoothForms.exists_local_log (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] :
    ∃ l : 𝔸 → 𝔸, ContDiffAt ℝ ∞ l 1 ∧ (∀ᶠ h in 𝓝 (1 : 𝔸), NormedSpace.exp (l h) = h) ∧
      ∀ᶠ X in 𝓝 (0 : 𝔸), l (NormedSpace.exp X) = X := by sorry
