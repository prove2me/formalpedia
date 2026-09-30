-- Prove2me | Theorems.Thm_LysgaardCVRP_Shrink_proposition_1
-- name    : LysgaardCVRP.Shrink.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:00:03.759+00:00
-- url     : https://prove2.me/theorems/e1231e2b-b48b-42ea-96f8-5f106fa8780c
-- title:
--   Proposition 1: shrinking $S$ with $x(\delta(S)) \le 2$ and $x(\delta(R)) \ge 2$ for all $R \subset S$ is safe
-- statement:
--   Consider the capacitated vehicle routing problem on the complete graph with vertex set $\{0, \dots, n\}$, depot $0$, vehicle capacity $Q > 0$ and customers $i = 1, \dots, n$ with integer demands $0 < q_i \le Q$. The capacity inequalities are $x(\delta(T)) \ge 2r(T)$ for customer sets $T$ with $|T| \ge 2$, where $r(T)$ is the bin-packing number of $T$.
--
--   Let $x \ge 0$ be an edge vector (an LP solution) and let $S$ be a customer set such that
--
--   $$x(\delta(S)) \le 2 \qquad\text{and}\qquad x(\delta(R)) \ge 2 \ \text{ for every nonempty } R \subsetneq S .$$
--
--   Then shrinking $S$ is safe for the separation of capacity inequalities: for every customer set $T$ with $|T| \ge 2$ and $x(\delta(T)) < 2r(T)$ there is a customer set $T'$ with $|T'| \ge 2$, with $S \subseteq T'$ or $S \cap T' = \emptyset$, such that
--
--   $$2r(T) - x(\delta(T)) \le 2r(T') - x(\delta(T')).$$
--
--   The proposition extends the classical rule that an edge $e$ with $x_e \ge 1$ may be shrunk to sets with more than two customers, so that separation heuristics may run on a smaller support graph without missing violated capacity inequalities.
--
--   **Formalization Note** Customer sets are finite sets of vertices not containing the depot. Of the LP point only $x \ge 0$ is assumed (the degree equations and upper bounds are not used), which makes the statement at least as strong as the paper's. The paper's "$\forall R \subset S$" is read over nonempty proper subsets: for $R = \emptyset$ the cut is $0 < 2$.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4), Proposition 1; definition of safe shrinking in §2.1, same page

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_binPackingNumber
import Definitions.Def_LysgaardCVRP_Shrink_SafeToShrink

namespace LysgaardCVRP.Shrink

/-- **Proposition 1** of Lysgaard, Letchford & Eglese, *A new branch-and-cut algorithm for the capacitated vehicle
routing problem*, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4): "For separation of capacity inequalities, it is
safe to shrink a customer set $S$ if $x^*(\delta(S)) \le 2$ and $x^*(\delta(R)) \ge 2$
$\forall R \subset S$."

The capacity inequalities are (2), $x(\delta(T)) \ge 2r(T)$ for customer sets $|T| \ge 2$, with
$r$ the bin-packing number; "safe" is the p. 426 notion `SafeToShrink`.

**Formalization Note.** Customer sets are `Finset`s of `Fin (n+1)` not containing the depot `0`. Standing
hypotheses of §1 (p. 423): $Q > 0$ real (the paper never says $Q$ is an integer) and integer demands
$0 < q_i \le Q$ for every customer. The LP point $x^*$ is only assumed nonnegative (the bounds of
(3)–(4)); the degree equations and upper bounds are not needed, so the statement holds for every
such $x$ and is at least as strong as the paper's. "$\forall R \subset S$" is read as every
**nonempty proper** subset $R$ of $S$: for $R = \emptyset$ one has $x(\delta(\emptyset)) = 0 < 2$, so
including it would make the hypothesis unsatisfiable. The empty set $S$ is not excluded; the conclusion is then trivially
true, so no hypothesis is needed. -/
theorem proposition_1 {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin (n + 1))) (hS0 : (0 : Fin (n + 1)) ∉ S) (hS : cut x S ≤ 2)
    (hR : ∀ R : Finset (Fin (n + 1)), R ⊆ S → R.Nonempty → R ≠ S → 2 ≤ cut x R) :
    SafeToShrink x (binPackingNumber q Q) S := by sorry

end LysgaardCVRP.Shrink
