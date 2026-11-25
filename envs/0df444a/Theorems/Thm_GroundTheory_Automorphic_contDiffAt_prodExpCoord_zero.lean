-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_contDiffAt_prodExpCoord_zero
-- name    : GroundTheory.Automorphic.contDiffAt_prodExpCoord_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:39.566883+00:00
-- url     : https://prove2.me/theorems/2c87f274-c3cd-4146-ba03-a3a10fd5a2f8
-- title:
--   Automorphic: cont Diff At prod Exp Coord zero
-- statement:
--   The Automorphic construction uses the cont Diff At prod Exp Coord zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L136-L139

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

theorem GroundTheory.Automorphic.contDiffAt_prodExpCoord_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiffAt ℝ ∞ (prodExpCoord b) 0 := by sorry
