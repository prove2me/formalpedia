-- Prove2me | Theorems.Thm_GlobalTheory_ZModPerp_exists_eq_nsmul_zmod
-- name    : GlobalTheory.ZModPerp.exists_eq_nsmul_zmod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:51.092804+00:00
-- url     : https://prove2.me/theorems/da45e789-6de5-4d9a-9560-57116d0f2cbb
-- title:
--   ZMod Perp: exists eq nsmul zmod
-- statement:
--   The ZMod Perp construction uses the exists eq nsmul zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_OrthogonalFreeOfPerfectAltZmod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory GlobalTheory.ZModPerp

theorem GlobalTheory.ZModPerp.exists_eq_nsmul_zmod {n r N : ℕ} [NeZero n] (h : r * N = n) (y : ZMod n)
    (hy : N • y = 0) : ∃ z : ZMod n, y = r • z := by sorry
