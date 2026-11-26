-- Prove2me | Theorems.Thm_MurtySimon_card_LC0_split
-- name    : MurtySimon.card_LC0_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:24.785011+00:00
-- url     : https://prove2.me/theorems/67204d1a-6a04-426e-a785-f18e5d4392ac
-- title:
--   Murty Simon: card LC0 split
-- statement:
--   The Murty Simon construction uses the card LC0 split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L144-L146
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L144-L146

module
public import Definitions.Def_MurtySimon_Bound
public import Definitions.Def_MurtySimon_Equality
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section

theorem MurtySimon.card_LC0_split (M : Finset (Sym2 V)) (C : (aux G ∅).ConnectedComponent) :
    #((LC0 C).filter (· ∉ M)) + #((LC0 C).filter (· ∈ M)) = cA G ∅ C := by sorry
