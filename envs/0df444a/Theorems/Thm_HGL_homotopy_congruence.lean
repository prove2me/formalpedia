-- Prove2me | Theorems.Thm_HGL_homotopy_congruence
-- name    : HGL.homotopy_congruence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:06:58.5802+00:00
-- url     : https://prove2.me/theorems/eaade7da-6ae5-4eaa-86fe-2d1a6390b697
-- title:
--   The link-homotopy relation is a congruence for the concatenation product (Lemma 3.4)
-- statement:
--   If two generalized string links are link-homotopic and two further generalized string links are link-homotopic, then their concatenations are link-homotopic. The elementary link-homotopy moves are compatible with concatenation on either side - carried by the world - and this one-sided compatibility lifts through the equivalence closure of the moves to the componentwise compatibility of products: link homotopy is a congruence for the concatenation product of the monoid of generalized string links, the algebraic form of Lemma 3.4.
-- source:
--   J. R. T. Theodoro de Lima, Homotopy of braids on surfaces: extending Goldsmith's answer to Artin, Journal of Knot Theory and Its Ramifications 28 (2019) 1950013, arXiv:1811.02006, Section 3 (Lemma 3.4).

import Mathlib
import Definitions.Def_HGL_alg
import Definitions.Def_HGL_tor

namespace HGL

/-!  Milestone 1 (Lemma 3.4): the link-homotopy equivalence relation is
compatible with concatenation: if two generalized string links are
link-homotopic, then so are the products with any other generalized string
link, on either side, and componentwise products of homotopic links are
homotopic. The proof lifts the one-sided compatibility of the elementary
moves through the equivalence closure by induction. -/
theorem homotopy_congruence {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∀ s t u v : S, EqvGen W.moves s t → EqvGen W.moves u v →
      EqvGen W.moves (s * u) (t * v) := by sorry

end HGL
