-- Prove2me | Theorems.Thm_MurtySimon_exists_onPath_of_triangle
-- name    : MurtySimon.exists_onPath_of_triangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:36.107482+00:00
-- url     : https://prove2.me/theorems/db2e3217-f5b4-594d-b64b-ad035bd1bc3a
-- title:
--   Murty Simon: exists on Path of triangle
-- statement:
--   **Lemma 2.2.** In a diameter-2-critical graph, every edge in a triangle lies on some critical
--   2-path.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L123-L171
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Basic.lean#L123-L171

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

theorem MurtySimon.exists_onPath_of_triangle (hG : IsCritical G) {x y w : V} (hxy : G.Adj x y)
    (hxw : G.Adj x w) (hwy : G.Adj w y) : ∃ f, OnPath G s(x, y) f := by sorry
