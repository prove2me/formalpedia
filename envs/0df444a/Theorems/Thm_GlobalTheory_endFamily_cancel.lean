-- Prove2me | Theorems.Thm_GlobalTheory_endFamily_cancel
-- name    : GlobalTheory.endFamily_cancel
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:16.691894+00:00
-- url     : https://prove2.me/theorems/6a155153-4736-405f-ae80-5bdc09e687b1
-- title:
--   Global Theory: end Family cancel
-- statement:
--   The Global Theory construction uses the end Family cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EndomorphismFamilyDirectSummandCancellation.lean#L15-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EndomorphismFamilyDirectSummandCancellation.lean#L15-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismFamilyDirectSummandCancellation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.endFamily_cancel : ∀ (k ι V V' U : Type) [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    [AddCommGroup U] [Module k U] [FiniteDimensional k U] (a : ι → Module.End k V)
    (b : ι → Module.End k V') (c : ι → Module.End k U),
    (∃ e : (V × U) ≃ₗ[k] (V' × U), ∀ i x, e ((a i).prodMap (c i) x) = (b i).prodMap (c i) (e x)) →
      ∃ e : V ≃ₗ[k] V', ∀ i x, e (a i x) = b i (e x) := by sorry
