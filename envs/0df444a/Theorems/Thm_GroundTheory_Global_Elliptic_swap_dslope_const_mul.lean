-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_swap_dslope_const_mul
-- name    : GroundTheory.Global.Elliptic.swap_dslope_const_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:08.66681+00:00
-- url     : https://prove2.me/theorems/3c4aa760-5d47-4040-9940-3f7b0ecb5240
-- title:
--   Elliptic: swap dslope const mul
-- statement:
--   The Elliptic construction uses the swap dslope const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L57-L65

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

theorem GroundTheory.Global.Elliptic.swap_dslope_const_mul (p a : ℂ) (g : ℂ → ℂ) :
    Function.swap dslope p (fun z ↦ a * g z) = fun z ↦ a * Function.swap dslope p g z := by sorry
