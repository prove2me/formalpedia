-- Prove2me | Theorems.Thm_MellinDuality_im_sum
-- name    : MellinDuality.im_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:43.369808+00:00
-- url     : https://prove2.me/theorems/9f624c3e-61e5-4b6a-a86c-f4b71e9a6a23
-- title:
--   Mellin Duality: im sum
-- statement:
--   The Mellin Duality construction uses the im sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L35-L39
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Quartic.lean#L35-L39

module
public import Definitions.Def_MellinDuality_Mellin
public import Definitions.Def_MellinDuality_Quartic
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem MellinDuality.im_sum {ι : Type*} (s : Finset ι) (f : ι → GaussianInt) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by sorry
