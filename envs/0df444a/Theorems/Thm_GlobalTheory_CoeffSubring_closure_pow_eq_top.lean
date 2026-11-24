-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_closure_pow_eq_top
-- name    : GlobalTheory.CoeffSubring.closure_pow_eq_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:14:51.891806+00:00
-- url     : https://prove2.me/theorems/b283db34-d54e-42b6-ae67-fcab18a2d979
-- title:
--   Coeff Subring: closure pow eq top
-- statement:
--   The Coeff Subring construction uses the closure pow eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L24-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L24-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {k : Type} [Field k] {p : ℕ} {B : Set k}

theorem GlobalTheory.CoeffSubring.closure_pow_eq_top (hp : p.Prime) (h0 : (p : k) = 0)
    (hB : Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤) (n : ℕ) :
    Subring.closure (Set.range (fun x : k => x ^ p ^ n) ∪ B) = ⊤ := by sorry
