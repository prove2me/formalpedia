-- Prove2me | Theorems.Thm_MurtySimon_pieces_nonneg
-- name    : MurtySimon.pieces_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:47.50578+00:00
-- url     : https://prove2.me/theorems/c3eee2f6-128d-59f2-af70-a8e4672c89c8
-- title:
--   Murty Simon: pieces nonneg
-- statement:
--   The Murty Simon construction uses the pieces nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L132-L142
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Equality.lean#L132-L142

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

theorem MurtySimon.pieces_nonneg (hG : IsCritical G) (heq : EqCase G) {M : Finset (Sym2 V)}
    (hmax : IsMaximalEdgeMatching G M) (C : (aux G ∅).ConnectedComponent) :
    cB G ∅ C ≤ #((LC0 C).filter (· ∉ M)) := by sorry
