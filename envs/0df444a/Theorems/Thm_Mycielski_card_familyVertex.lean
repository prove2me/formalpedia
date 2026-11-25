-- Prove2me | Theorems.Thm_Mycielski_card_familyVertex
-- name    : Mycielski.card_familyVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:26:33.871842+00:00
-- url     : https://prove2.me/theorems/47044b5b-9127-4d06-bfd3-0d39d2a0d7da
-- title:
--   Mycielski: card family Vertex
-- statement:
--   The family has `3 * 2^n - 1` vertices, without truncated subtraction.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Family.lean#L39-L46
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Family.lean#L39-L46

module
public import Definitions.Def_Mycielski_Coloring
public import Definitions.Def_Mycielski_Family
set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph

theorem Mycielski.card_familyVertex (n : ℕ) :
    Fintype.card (FamilyVertex n) + 1 = 3 * 2 ^ n := by sorry
