-- Prove2me | Theorems.Thm_GlobalTheory_padicToO_unique
-- name    : GlobalTheory.padicToO_unique
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:38.744555+00:00
-- url     : https://prove2.me/theorems/0fe841df-750d-438c-8b79-072bf559ff84
-- title:
--   Global Theory: padic To O unique
-- statement:
--   The Global Theory construction uses the padic To O unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicRingHomEqCanonical.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PadicRingHomEqCanonical.lean#L23-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PadicRingHomEqCanonical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory

theorem GlobalTheory.padicToO_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (g : ℤ_[p] →+* O), g = padicToO p O := by sorry
