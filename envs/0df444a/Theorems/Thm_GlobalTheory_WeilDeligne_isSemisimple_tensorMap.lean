-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_tensorMap
-- name    : GlobalTheory.WeilDeligne.isSemisimple_tensorMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:56:42.71291+00:00
-- url     : https://prove2.me/theorems/d96b3af9-37be-46cb-9c3e-cd0b3226793b
-- title:
--   Weil Deligne: is Semisimple tensor Map
-- statement:
--   The Weil Deligne construction uses the is Semisimple tensor Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L49-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsSemisimpleOfISupEigenspace.lean#L49-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem GlobalTheory.WeilDeligne.isSemisimple_tensorMap [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] {f : End ℂ V}
    {g : End ℂ V'} (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    End.IsSemisimple (TensorProduct.map f g : End ℂ (V ⊗[ℂ] V')) := by sorry
