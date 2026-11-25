-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_contDiff_smul_of_tsupport
-- name    : GroundTheory.Automorphic.contDiff_smul_of_tsupport
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:38.995199+00:00
-- url     : https://prove2.me/theorems/88d01cfd-c314-44df-a1a9-6bc0cc0dee53
-- title:
--   Automorphic: cont Diff smul of tsupport
-- statement:
--   The Automorphic construction uses the cont Diff smul of tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L258-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L258-L270

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

theorem GroundTheory.Automorphic.contDiff_smul_of_tsupport {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {O : Set V} (hO : IsOpen O) {f : V → F}
    {g : V → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiff ℝ ∞ g) (hgO : tsupport g ⊆ O) :
    ContDiff ℝ ∞ (fun x => g x • f x) := by sorry
