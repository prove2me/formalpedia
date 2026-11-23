-- Prove2me | Theorems.Thm_GlobalTheory_ZModPerp_baer_zmod
-- name    : GlobalTheory.ZModPerp.baer_zmod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:34.118904+00:00
-- url     : https://prove2.me/theorems/a7ee2d53-cf30-489c-a6c1-fb103a43f471
-- title:
--   ZMod Perp: baer zmod
-- statement:
--   The ZMod Perp construction uses the baer zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L43-L55

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

theorem GlobalTheory.ZModPerp.baer_zmod (n : ℕ) [NeZero n] : Module.Baer (ZMod n) (ZMod n) := by sorry
