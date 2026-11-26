-- Prove2me | Theorems.Thm_MurtySimon_onPath_iff
-- name    : MurtySimon.onPath_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:02.879042+00:00
-- url     : https://prove2.me/theorems/12358f05-c127-4281-a6cb-db44c58a1144
-- title:
--   Murty Simon: on Path iff
-- statement:
--   The edges on the critical 2-path `(x, u, y)` are `xu` and `uy`.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L91-L102
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L91-L102

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}

theorem MurtySimon.onPath_iff {x y u : V} (h : IsMid G x y u) {e : Sym2 V} :
    OnPath G e s(x, y) ↔ e = s(x, u) ∨ e = s(u, y) := by sorry
