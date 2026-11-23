-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_contDiff_det_pi
-- name    : GroundTheory.Automorphic.contDiff_det_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:35.026918+00:00
-- url     : https://prove2.me/theorems/ad00e071-a130-42a9-a44d-35ef3bf9e9c0
-- title:
--   Automorphic: cont Diff det pi
-- statement:
--   The Automorphic construction uses the cont Diff det pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L242-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L242-L256

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

theorem GroundTheory.Automorphic.contDiff_det_pi {d : ℕ} :
    ContDiff ℝ ∞ (fun f : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) => f.det) := by sorry
