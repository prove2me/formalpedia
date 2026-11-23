-- Prove2me | Theorems.Thm_GlobalTheory_ZModPerp_exists_dual_ne_zero
-- name    : GlobalTheory.ZModPerp.exists_dual_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:19.484718+00:00
-- url     : https://prove2.me/theorems/d18dc716-c570-4af6-a489-91d4172efae1
-- title:
--   ZMod Perp: exists dual ne zero
-- statement:
--   The ZMod Perp construction uses the exists dual ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L57-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L57-L79

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

theorem GlobalTheory.ZModPerp.exists_dual_ne_zero {n : ℕ} [NeZero n] {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    {q : M} (hq : q ≠ 0) : ∃ f : Dual (ZMod n) M, f q ≠ 0 := by sorry
