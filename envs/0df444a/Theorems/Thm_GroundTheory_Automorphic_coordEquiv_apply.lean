-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coordEquiv_apply
-- name    : GroundTheory.Automorphic.coordEquiv_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:19.647536+00:00
-- url     : https://prove2.me/theorems/a1a04248-7e46-42a0-9141-cbd85fb715da
-- title:
--   Automorphic: coord Equiv apply
-- statement:
--   The Automorphic construction uses the coord Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ContDiffCompCoordEquiv.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ContDiffCompCoordEquiv.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem GroundTheory.Automorphic.coordEquiv_apply {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (x : EuclideanSpace ℝ (Fin d)) :
    coordEquiv b x = ∑ j, x j • b j := by sorry
