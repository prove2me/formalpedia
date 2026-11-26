-- Prove2me | Theorems.Thm_MurtySimon_isMid_of_isCrit
-- name    : MurtySimon.isMid_of_isCrit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:58:17.607802+00:00
-- url     : https://prove2.me/theorems/7927a1b4-7e3b-463d-8b67-0339e6c7fc52
-- title:
--   Murty Simon: is Mid of is Crit
-- statement:
--   A non-edge with a common neighbour `w` is critical iff `w` is its unique common neighbour.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L110-L115
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Bound.lean#L110-L115

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

theorem MurtySimon.isMid_of_isCrit {x y w : V} (h : IsCrit G s(x, y)) (hxw : G.Adj x w) (hwy : G.Adj w y) :
    IsMid G x y w := by sorry
