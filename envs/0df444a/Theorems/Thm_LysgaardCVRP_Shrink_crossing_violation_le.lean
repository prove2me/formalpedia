-- Prove2me | Theorems.Thm_LysgaardCVRP_Shrink_crossing_violation_le
-- name    : LysgaardCVRP.Shrink.crossing_violation_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T16:55:00.745691+00:00
-- url     : https://prove2.me/theorems/5a3114c8-4ded-4ca1-8aea-d94d38b79541
-- title:
--   Crossing sets: the capacity inequality on $S \cup T$ is violated at least as much as on $T$
-- statement:
--   Let $Q > 0$, let the customers have integer demands $0 < q_i \le Q$, let $x \ge 0$ be an edge vector, and let $S$ be a customer set with
--
--   1. $x(\delta(S)) \le 2$, and
--   2. $x(\delta(R)) \ge 2$ for every nonempty proper subset $R \subsetneq S$.
--
--   Let $T$ be a customer set that **crosses** $S$, i.e. $T \cap S$, $T \setminus S$ and $S \setminus T$ are all nonempty. Then, with $r$ the bin-packing number,
--
--   $$2r(T) - x(\delta(T)) \le 2r(S \cup T) - x(\delta(S \cup T)),$$
--
--   that is, the capacity inequality on $S \cup T$ is violated by at least as much as the capacity inequality on $T$.
--
--   This is the core of the proof of Proposition 1: a violated capacity inequality whose set crosses $S$ can be replaced by one whose set contains $S$.
--
--   **Formalization Note** Customer sets do not contain the depot. The condition "$\forall R \subset S$" is read over nonempty proper subsets, since $x(\delta(\emptyset)) = 0$. Only $x \ge 0$ is assumed of the LP point.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4), proof of Proposition 1

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_binPackingNumber
import Definitions.Def_LysgaardCVRP_Shrink_violation

namespace LysgaardCVRP.Shrink

/-- The crossing-set step of the proof of Proposition 1 of Lysgaard, Letchford & Eglese, *A new branch-and-cut algorithm for the capacitated vehicle
routing problem*, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4) (unnumbered):
"Let $T$ be a customer set which crosses $S$, i.e., such that $T \cap S$, $T \setminus S$ and
$S \setminus T$ are all non-empty. We show that the capacity inequality on $S \cup T$ is violated
by at least as much as the capacity inequality on $T$."

Under the hypotheses of Proposition 1 on $x$ and $S$ ($x(\delta(S)) \le 2$ and
$x(\delta(R)) \ge 2$ for every nonempty proper subset $R$ of $S$), every customer set $T$ crossing
$S$ satisfies $2r(T) - x(\delta(T)) \le 2r(S \cup T) - x(\delta(S \cup T))$.

**Formalization Note.** Customer sets are `Finset`s of `Fin (n+1)` not containing the depot `0`. Standing
hypotheses of §1 (p. 423): $Q > 0$ real (the paper never says $Q$ is an integer) and integer demands
$0 < q_i \le Q$ for every customer. The LP point $x^*$ is only assumed nonnegative (the bounds of
(3)–(4)); the degree equations and upper bounds are not needed, so the statement holds for every
such $x$ and is at least as strong as the paper's. "$\forall R \subset S$" is read as every
**nonempty proper** subset $R$ of $S$: for $R = \emptyset$ one has $x(\delta(\emptyset)) = 0 < 2$, so
including it would make the hypothesis unsatisfiable. -/
theorem crossing_violation_le {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin (n + 1))) (hS0 : (0 : Fin (n + 1)) ∉ S) (hS : cut x S ≤ 2)
    (hR : ∀ R : Finset (Fin (n + 1)), R ⊆ S → R.Nonempty → R ≠ S → 2 ≤ cut x R)
    (T : Finset (Fin (n + 1))) (hT0 : (0 : Fin (n + 1)) ∉ T)
    (hTS : (T ∩ S).Nonempty) (hTmS : (T \ S).Nonempty) (hSmT : (S \ T).Nonempty) :
    violation x (binPackingNumber q Q) T ≤ violation x (binPackingNumber q Q) (S ∪ T) := by sorry

end LysgaardCVRP.Shrink
