-- Prove2me | Theorems.Thm_MurtySimon_sum_pieces
-- name    : MurtySimon.sum_pieces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:01.061837+00:00
-- url     : https://prove2.me/theorems/91845cc1-4201-4e9a-be5a-28917d2a3075
-- title:
--   Murty Simon: sum pieces
-- statement:
--   The Murty Simon construction uses the sum pieces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L87-L124
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L87-L124

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

theorem MurtySimon.sum_pieces (M : Finset (Sym2 V)) (C : (aux G ∅).ConnectedComponent) :
    ∑ D ∈ (univ : Finset (aux G M).ConnectedComponent).filter (fun D => emb G M D = C),
      ((cA G M D : ℤ) - cB G M D) = (#((LC0 C).filter (· ∉ M)) : ℤ) - cB G ∅ C := by sorry
