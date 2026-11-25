-- Prove2me | Theorems.Thm_GlobalTheory_T_invertible_of_faithfully_flat
-- name    : GlobalTheory.T.invertible_of_faithfully_flat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:06.468107+00:00
-- url     : https://prove2.me/theorems/7587b7dd-fffd-49d3-894d-5fd2a09f0b06
-- title:
--   T: invertible of faithfully flat
-- statement:
--   The T construction uses the invertible of faithfully flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvertibleOfFaithfullyFlatStatement.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvertibleOfFaithfullyFlatStatement.lean#L6-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvertibleOfFaithfullyFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvertibleOfFaithfullyFlatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.invertible_of_faithfully_flat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [IsNoetherianRing B] [Module.FaithfullyFlat B B']
    (M : Type) [AddCommGroup M] [Module B M], Module.Invertible B' (B' ⊗[B] M) → Module.Invertible B M := by sorry
