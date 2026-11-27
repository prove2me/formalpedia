-- Prove2me | Theorems.Thm_GlobalTheory_ainf_isDomain_and_mu_ne_zero
-- name    : GlobalTheory.ainf_isDomain_and_mu_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:24.766217+00:00
-- url     : https://prove2.me/theorems/3e2dc44a-82fe-5d3e-b71f-06dc34ec801d
-- title:
--   Global Theory: ainf is Domain and mu ne zero
-- statement:
--   The Global Theory construction uses the ainf is Domain and mu ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AinfIsDomainMuNeZero.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AinfIsDomainMuNeZero.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SandwichMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AinfIsDomainMuNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
open GlobalTheory

theorem GlobalTheory.ainf_isDomain_and_mu_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by sorry
