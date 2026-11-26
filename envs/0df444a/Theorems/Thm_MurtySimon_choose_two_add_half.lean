-- Prove2me | Theorems.Thm_MurtySimon_choose_two_add_half
-- name    : MurtySimon.choose_two_add_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:03.190324+00:00
-- url     : https://prove2.me/theorems/9876d402-a9a4-5596-9eff-b31b631b3436
-- title:
--   Murty Simon: choose two add half
-- statement:
--   The Murty Simon construction uses the choose two add half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L57-L70
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L57-L70

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem MurtySimon.choose_two_add_half (n : ℕ) : n.choose 2 + n / 2 = 2 * (n ^ 2 / 4) := by sorry
