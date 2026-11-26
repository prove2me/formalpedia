-- Prove2me | Theorems.Thm_MurtySimon_two_le_compWt_of_safe
-- name    : MurtySimon.two_le_compWt_of_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:40.576514+00:00
-- url     : https://prove2.me/theorems/4f3e8fa0-d140-4cbc-bbd6-34f1bad84d46
-- title:
--   Murty Simon: two le comp Wt of safe
-- statement:
--   The Murty Simon construction uses the two le comp Wt of safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L182-L186
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L182-L186

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

theorem MurtySimon.two_le_compWt_of_safe {C : (aux G M).ConnectedComponent} {p : V × V}
    (hp : p ∈ exits G M) (hpC : compOf G M p = C) (hs : ¬ Covered M p.2) : 2 ≤ compWt C := by sorry
