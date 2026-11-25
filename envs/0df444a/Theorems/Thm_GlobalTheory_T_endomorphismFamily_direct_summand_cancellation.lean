-- Prove2me | Theorems.Thm_GlobalTheory_T_endomorphismFamily_direct_summand_cancellation
-- name    : GlobalTheory.T.endomorphismFamily_direct_summand_cancellation
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:33:11.025788+00:00
-- url     : https://prove2.me/theorems/7c89cbc5-fad5-4512-812d-31de8363f069
-- title:
--   T: endomorphism Family direct summand cancellation
-- statement:
--   The T construction uses the endomorphism Family direct summand cancellation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EndomorphismFamilyDirectSummandCancellationStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EndomorphismFamilyDirectSummandCancellationStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismFamilyDirectSummandCancellation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismFamilyDirectSummandCancellationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.endomorphismFamily_direct_summand_cancellation : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V'] [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V) (b : ι → Module.End k V') (c : ι → Module.End k U), (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) → ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by sorry
