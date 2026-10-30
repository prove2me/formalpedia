-- Prove2me | Theorems.Thm_HofmannStreicher1994_universe_presentations_equivalent
-- name    : HofmannStreicher1994.universe_presentations_equivalent
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-29T06:17:38.720075+00:00
-- url     : https://prove2.me/theorems/0c2a2767-1224-4e13-bc07-a7637e6b38c5
-- title:
--   Section 2.3: Equivalent presentations of the total universe family
-- statement:
--   At every universe level, the categorical disjoint union of all small groupoids is equivalent to the Grothendieck construction of the generic decoding family over the discrete universe of small groupoids. This asserts existence of an equivalence of categories. It compares two explicit semantic presentations and does not identify either with a constructed interpretation of a syntax expression.
-- source:
--   Hofmann and Streicher, A Groupoid Model Refutes Uniqueness of Identity Proofs, author manuscript dated 21 March 1994, https://www.dcs.ed.ac.uk/home/mxh/SH.dvi.gz; LICS 1994, https://doi.org/10.1109/LICS.1994.316071. Section 2, manuscript pp. 3–4, Grothendieck construction; Section 2.3, p. 7, discrete universe and generic family. Supporting comparison of the two explicit presentations, not a separately numbered source theorem.

import Definitions.Def_HofmannStreicher1994_Groupoids
open CategoryTheory
universe u

namespace HofmannStreicher1994

theorem universe_presentations_equivalent :
    Nonempty (UniverseTotal.{u} ≌ UniverseGrothendieck.{u}) := by sorry

end HofmannStreicher1994
