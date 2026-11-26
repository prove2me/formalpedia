-- Prove2me | Theorems.Thm_MellinDuality_natCast_inj_of_mem
-- name    : MellinDuality.natCast_inj_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:50.591794+00:00
-- url     : https://prove2.me/theorems/6b76ee7d-c26a-48f8-8759-5c91784c28fd
-- title:
--   Mellin Duality: nat Cast inj of mem
-- statement:
--   The Mellin Duality construction uses the nat Cast inj of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Parseval.lean#L29-L37
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Parseval.lean#L29-L37

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Parseval
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.natCast_inj_of_mem {n n' : ℕ} (hn : n ∈ Icc 1 ((p - 1) / 2))
    (hn' : n' ∈ Icc 1 ((p - 1) / 2)) : (n : ZMod p) = n' ↔ n = n' := by sorry
