-- Prove2me | Theorems.Thm_Mycielski_exists_triangleFree_chromaticNumber_ge
-- name    : Mycielski.exists_triangleFree_chromaticNumber_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:26:31.830805+00:00
-- url     : https://prove2.me/theorems/66960af9-2932-4222-a160-59316c87353d
-- title:
--   Mycielski: exists triangle Free chromatic Number ge
-- statement:
--   Finite triangle-free graphs have unbounded chromatic number.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Family.lean#L78-L90
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Family.lean#L78-L90

module
public import Definitions.Def_Mycielski_Coloring
public import Definitions.Def_Mycielski_Family
set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph

theorem Mycielski.exists_triangleFree_chromaticNumber_ge (k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 3 ∧ (k : ℕ∞) ≤ G.chromaticNumber := by sorry
