-- Prove2me | Theorems.Thm_MurtySimon_mem_neighborFinset_right
-- name    : MurtySimon.mem_neighborFinset_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:06.639948+00:00
-- url     : https://prove2.me/theorems/bf8a0e2f-0b39-4adc-92eb-76340926527f
-- title:
--   Murty Simon: mem neighbor Finset right
-- statement:
--   The neighbours of a right vertex `xy` with critical 2-path `(x, u, y)` are the edges of the
--   path outside `M`.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L65-L73
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Components.lean#L65-L73

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section

theorem MurtySimon.mem_neighborFinset_right {M : Finset (Sym2 V)} {x y u : V} (h : IsMid G x y u)
    {e : Sym2 V} : e ∈ (aux G M).neighborFinset s(x, y) ↔ (e = s(x, u) ∨ e = s(u, y)) ∧ e ∉ M := by sorry
