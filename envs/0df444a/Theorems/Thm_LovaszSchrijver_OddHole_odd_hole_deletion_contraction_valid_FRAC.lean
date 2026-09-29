-- Prove2me | Theorems.Thm_LovaszSchrijver_OddHole_odd_hole_deletion_contraction_valid_FRAC
-- name    : LovaszSchrijver.OddHole.odd_hole_deletion_contraction_valid_FRAC
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:48:13.725893+00:00
-- url     : https://prove2.me/theorems/f0fcfa25-cd5c-48c1-a67c-b12d7d361ab1
-- title:
--   Part (1) of the proof of Theorem 2.3 — deletion and contraction of an odd hole constraint are valid for FRAC(G)
-- statement:
--   Let $G = (V, E)$ be a finite graph with no isolated nodes, let $C \subseteq V$ induce a chordless odd cycle in $G$, and consider the odd hole constraint
--   $$\sum_{j \in C} x_j \le \tfrac12(|C| - 1).$$
--   For every $i \in C$:
--
--   1. its deletion, $\sum_{j \in C \setminus \{i\}} x_j \le \tfrac12(|C|-1)$, is valid for $\mathrm{FRAC}(G)$;
--   2. its contraction, $\sum_{j \in C \setminus (\Gamma(i) \cup \{i\})} x_j \le \tfrac12(|C|-1) - 1$, is valid for $\mathrm{FRAC}(G)$.
--
--   Together with Lemma 2.2 this shows that every odd hole constraint is valid for $N(G)$, the easy half of Theorem 2.3.
--
--   **Formalization Note** The odd hole constraint is the coefficient vector $\chi^C$ (the indicator of $C$) with right-hand side $(|C|-1)/2$; deletion and contraction are the same-graph coefficient vectors, and the contraction's right-hand side is $b - a_i = (|C|-1)/2 - 1$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 178, part (1) of the proof of Theorem 2.3

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones
import Definitions.Def_LovaszSchrijver_OddHole_OddHole
import Definitions.Def_LovaszSchrijver_OddHole_DeletionContraction

namespace LovaszSchrijver.OddHole

/-- Part (1) of the proof of Theorem 2.3 (p. 178): for an odd hole `C` and any `i ∈ C`,
both the deletion and the contraction of `i` in the odd hole constraint
`∑_{j ∈ C} x_j ≤ (|C| − 1)/2` are valid for `FRAC(G)`. -/
theorem odd_hole_deletion_contraction_valid_FRAC {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (C : Finset V) (hC : IsOddHole G C) (i : V) (hi : i ∈ C) :
    Valid (FRAC G) (deletion (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2) ∧
      Valid (FRAC G) (contraction G (fun j => if j ∈ C then (1 : ℝ) else 0) i)
        (((C.card : ℝ) - 1) / 2 - 1) := by sorry

end LovaszSchrijver.OddHole
