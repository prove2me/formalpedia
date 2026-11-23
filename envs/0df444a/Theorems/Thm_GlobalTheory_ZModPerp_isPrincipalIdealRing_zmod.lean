-- Prove2me | Theorems.Thm_GlobalTheory_ZModPerp_isPrincipalIdealRing_zmod
-- name    : GlobalTheory.ZModPerp.isPrincipalIdealRing_zmod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:52.701551+00:00
-- url     : https://prove2.me/theorems/f0915152-c141-4b21-b6dc-d6f622acee8e
-- title:
--   ZMod Perp: is Principal Ideal Ring zmod
-- statement:
--   The ZMod Perp construction uses the is Principal Ideal Ring zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L40-L41

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

theorem GlobalTheory.ZModPerp.isPrincipalIdealRing_zmod (n : ℕ) : IsPrincipalIdealRing (ZMod n) := by sorry
