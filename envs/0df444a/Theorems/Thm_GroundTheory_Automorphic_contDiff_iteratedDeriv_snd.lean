-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_contDiff_iteratedDeriv_snd
-- name    : GroundTheory.Automorphic.contDiff_iteratedDeriv_snd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:40.068751+00:00
-- url     : https://prove2.me/theorems/947fd769-c357-49ea-bc5d-c485272d1796
-- title:
--   Automorphic: cont Diff iterated Deriv snd
-- statement:
--   The Automorphic construction uses the cont Diff iterated Deriv snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L13-L36

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem GroundTheory.Automorphic.contDiff_iteratedDeriv_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℕ) :
    ∀ {Ψ : E × ℝ → F}, ContDiff ℝ ∞ Ψ → ∀ s : ℝ,
      ContDiff ℝ ∞ (fun Y : E => iteratedDeriv p (fun t : ℝ => Ψ (Y, t)) s) := by sorry
