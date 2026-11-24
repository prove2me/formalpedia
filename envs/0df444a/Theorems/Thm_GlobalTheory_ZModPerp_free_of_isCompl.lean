-- Prove2me | Theorems.Thm_GlobalTheory_ZModPerp_free_of_isCompl
-- name    : GlobalTheory.ZModPerp.free_of_isCompl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:32.207204+00:00
-- url     : https://prove2.me/theorems/d42a21b6-90e7-4f53-9513-e1f362042932
-- title:
--   ZMod Perp: free of is Compl
-- statement:
--   The ZMod Perp construction uses the free of is Compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L98-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/OrthogonalFreeOfPerfectAltZmod.lean#L98-L116

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

theorem GlobalTheory.ZModPerp.free_of_isCompl {R M : Type*} [CommRing R] [Finite (MaximalSpectrum R)] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] {T T' : Submodule R M} [Module.Free R T]
    (h : IsCompl T T') : Module.Free R T' := by sorry
