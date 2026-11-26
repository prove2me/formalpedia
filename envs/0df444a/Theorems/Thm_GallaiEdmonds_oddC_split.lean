-- Prove2me | Theorems.Thm_GallaiEdmonds_oddC_split
-- name    : GallaiEdmonds.oddC_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:44.891146+00:00
-- url     : https://prove2.me/theorems/cc54326e-be70-5cb2-a786-5d2771b1ab1b
-- title:
--   Gallai Edmonds: odd C split
-- statement:
--   Splitting `W` into a closed part and its complement splits the odd components.
--
--   Source: https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L167-L195
-- source:
--   https://github.com/jtraverso/berge-matching/blob/f01d042c071c778fb3f432312356136a92369076/GallaiEdmondsLib/GEComponents.lean#L167-L195

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}

theorem GallaiEdmonds.oddC_split [Finite V] (hW : W' ⊆ W) (hc : Closed G W W') :
    oddC G W = oddC G W' + oddC G (W \ W') := by sorry
