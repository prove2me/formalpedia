-- Prove2me | Theorems.Thm_GlobalTheory_FFDescent_invertible_of_invertible_baseChange
-- name    : GlobalTheory.FFDescent.invertible_of_invertible_baseChange
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:18:32.999407+00:00
-- url     : https://prove2.me/theorems/51c55528-814d-4297-aa55-0400b55633dd
-- title:
--   FFDescent: invertible of invertible base Change
-- statement:
--   The FFDescent construction uses the invertible of invertible base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvertibleOfFaithfullyFlat.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvertibleOfFaithfullyFlat.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvertibleOfFaithfullyFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.FFDescent

theorem GlobalTheory.FFDescent.invertible_of_invertible_baseChange : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [IsNoetherianRing B] [Module.FaithfullyFlat B B']
    (M : Type) [AddCommGroup M] [Module B M], Module.Invertible B' (B' ⊗[B] M) → Module.Invertible B M := by sorry
