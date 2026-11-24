-- Prove2me | Theorems.Thm_GlobalTheory_TensHead_MinStab_map
-- name    : GlobalTheory.TensHead.MinStab.map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:52.866804+00:00
-- url     : https://prove2.me/theorems/a34c3336-2403-4831-ac37-2a7c72c83988
-- title:
--   Min Stab: map
-- statement:
--   The Min Stab construction uses the map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeKerOfLocalFiniteLengthToSimple.lean#L15-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeKerOfLocalFiniteLengthToSimple.lean#L15-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.TensHead.MinStab.map {A : Set (Module.End ℂ W)} {T : Submodule ℂ W} (hT : MinStab A T)
    (b : Module.End ℂ W) (hb : ∀ a ∈ A, a * b = b * a) : MinStab A (T.map b) := by sorry
