-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_residue_comp_mul
-- name    : GroundTheory.Global.Elliptic.residue_comp_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:29.547646+00:00
-- url     : https://prove2.me/theorems/d195efa1-83b8-4e82-8b71-c38b6fb69dbd
-- title:
--   Elliptic: residue comp mul
-- statement:
--   The Elliptic construction uses the residue comp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L257-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L257-L277

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic

theorem GroundTheory.Global.Elliptic.residue_comp_mul {f : ℂ → ℂ} {c w₀ : ℂ} (hc : c ≠ 0) (hf : MeromorphicAt f (c * w₀)) :
    residue (fun w ↦ f (c * w)) w₀ = c⁻¹ * residue f (c * w₀) := by sorry
