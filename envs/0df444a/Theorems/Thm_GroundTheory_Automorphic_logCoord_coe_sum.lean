-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_logCoord_coe_sum
-- name    : GroundTheory.Automorphic.logCoord_coe_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:28.202452+00:00
-- url     : https://prove2.me/theorems/6472436f-c196-4033-a278-6e4f2b56b242
-- title:
--   Automorphic: log Coord coe sum
-- statement:
--   The Automorphic construction uses the log Coord coe sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L98-L103

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

theorem GroundTheory.Automorphic.logCoord_coe_sum {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) :
    b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 (∑ i, t i • (b i : 𝔸))) = t := by sorry
