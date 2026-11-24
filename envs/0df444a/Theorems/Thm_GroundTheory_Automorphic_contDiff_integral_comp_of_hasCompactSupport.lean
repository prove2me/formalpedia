-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_contDiff_integral_comp_of_hasCompactSupport
-- name    : GroundTheory.Automorphic.contDiff_integral_comp_of_hasCompactSupport
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:39.859438+00:00
-- url     : https://prove2.me/theorems/aad7c2d1-3ebc-4b0c-aacb-edea9a49e850
-- title:
--   Automorphic: cont Diff integral comp of has Compact Support
-- statement:
--   The Automorphic construction uses the cont Diff integral comp of has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L274-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L274-L320

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
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
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
open MeasureTheory

theorem GroundTheory.Automorphic.contDiff_integral_comp_of_hasCompactSupport {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X] (ν : Measure X)
    [IsFiniteMeasure ν] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : X → V}
    (hu : Continuous u) (n : ℕ) :
    ∀ {W F : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [CompleteSpace F] (Ξ : V × W → F), ContDiff ℝ ∞ Ξ → HasCompactSupport Ξ →
      ContDiff ℝ n (fun z => ∫ x, Ξ (u x, z) ∂ν) := by sorry
