-- Prove2me | Theorems.Thm_MurtySimon_two_le_compWt_of_two
-- name    : MurtySimon.two_le_compWt_of_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:20.970597+00:00
-- url     : https://prove2.me/theorems/836415aa-df30-4b0b-a229-7aebe143b7d1
-- title:
--   Murty Simon: two le comp Wt of two
-- statement:
--   The Murty Simon construction uses the two le comp Wt of two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L188-L198
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L188-L198

module
public import Definitions.Def_MurtySimon_Components
public import Definitions.Def_MurtySimon_Bound
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
variable {M : Finset (Sym2 V)}

theorem MurtySimon.two_le_compWt_of_two {C : (aux G M).ConnectedComponent} {p q : V × V}
    (hp : p ∈ exits G M) (hpC : compOf G M p = C) (hq : q ∈ exits G M) (hqC : compOf G M q = C)
    (hpq : p ≠ q) : 2 ≤ compWt C := by sorry
