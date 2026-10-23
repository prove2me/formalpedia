-- Prove2me | Theorems.Thm_MICPRep_Periodic_proposition_5_3_union
-- name    : MICPRep.Periodic.proposition_5_3_union
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:09.330948+00:00
-- url     : https://prove2.me/theorems/fb3a0a8d-36c8-4182-8373-114a99a27b16
-- title:
--   Proposition 5.3 (finite unions, binary MICP-R), p. 17 — a finite union of binary MICP-R sets is binary MICP-R
-- statement:
--   Let $S_1, \dots, S_k \subseteq \mathbb R^n$ ($k \in \mathbb Z_+$) be binary MICP-R sets. Then
--   $$\bigcup_{i=1}^k S_i$$
--   is binary MICP-R.
--
--   This is the finite-union clause of Proposition 5.3; it lets the proof of Proposition 6.1 merge the binary pieces produced at each induction step into one binary MICP-R set.
--
--   **Formalization Note** Only this clause of Proposition 5.3 is stated; the closure properties under affine maps, products, Minkowski sums and intersections, and the unions of the other classes, are not part of this item. The empty union ($k = 0$) is included.
-- source:
--   Lubin, Vielma, Zadik, Mixed-integer convex representability, arXiv:1706.05135v3, p. 17, Proposition 5.3 (finite-union clause for binary MICP-R sets)

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

namespace MICPRep.Periodic

open scoped ENNReal Matrix

/-- Proposition 5.3, p. 17 (finite-union clause for binary MICP-R sets). -/
theorem proposition_5_3_union {n k : ℕ} (S : Fin k → Set (Pt n))
    (hS : ∀ i, IsBinaryMICPR (S i)) :
    IsBinaryMICPR (⋃ i, S i) := by sorry

end MICPRep.Periodic
