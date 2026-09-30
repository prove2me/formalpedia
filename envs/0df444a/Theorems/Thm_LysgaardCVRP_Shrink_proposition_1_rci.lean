-- Prove2me | Theorems.Thm_LysgaardCVRP_Shrink_proposition_1_rci
-- name    : LysgaardCVRP.Shrink.proposition_1_rci
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T17:07:47.200852+00:00
-- url     : https://prove2.me/theorems/b347a5b7-9dd7-4bdf-a27c-b85b84e4510b
-- title:
--   Proposition 1 for rounded capacity inequalities
-- statement:
--   Under the hypotheses of Proposition 1 ($Q > 0$, integer demands $0 < q_i \le Q$, $x \ge 0$, and a customer set $S$ with $x(\delta(S)) \le 2$ and $x(\delta(R)) \ge 2$ for every nonempty $R \subsetneq S$), shrinking $S$ is also safe for the separation of the **rounded capacity inequalities**
--
--   $$x(\delta(T)) \ge 2k(T), \qquad k(T) = \left\lceil \frac{q(T)}{Q} \right\rceil, \qquad T \subseteq V_c,\ |T| \ge 2 .$$
--
--   That is, for every customer set $T$ with $|T| \ge 2$ and $x(\delta(T)) < 2k(T)$ there is a customer set $T'$ with $|T'| \ge 2$, with $S \subseteq T'$ or $S \cap T' = \emptyset$, such that $2k(T) - x(\delta(T)) \le 2k(T') - x(\delta(T'))$.
--
--   This is the form used by the algorithm, which separates rounded capacity inequalities rather than capacity inequalities.
--
--   **Formalization Note** Same conventions as Proposition 1.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4), sentence following the proof of Proposition 1

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_LysgaardCVRP_Shrink_SafeToShrink

namespace LysgaardCVRP.Shrink

/-- Proposition 1 for rounded capacity inequalities, Lysgaard, Letchford & Eglese, *A new branch-and-cut algorithm for the capacitated vehicle
routing problem*, Math. Program. Ser. A 100 (2004), p. 426 (PDF p. 4), the sentence after
the proof of Proposition 1 (unnumbered): "We note that the condition for safe shrinking in
proposition 1 also applies to RCIs."

The rounded capacity inequalities (RCIs) are $x(\delta(T)) \ge 2k(T)$, $k(T) = \lceil q(T)/Q \rceil$,
for customer sets $|T| \ge 2$ (§1, p. 424, and §2.1, p. 426). Under the hypotheses of Proposition 1
it is safe to shrink $S$ for the separation of RCIs.

**Formalization Note.** Customer sets are `Finset`s of `Fin (n+1)` not containing the depot `0`. Standing
hypotheses of §1 (p. 423): $Q > 0$ real (the paper never says $Q$ is an integer) and integer demands
$0 < q_i \le Q$ for every customer. The LP point $x^*$ is only assumed nonnegative (the bounds of
(3)–(4)); the degree equations and upper bounds are not needed, so the statement holds for every
such $x$ and is at least as strong as the paper's. "$\forall R \subset S$" is read as every
**nonempty proper** subset $R$ of $S$: for $R = \emptyset$ one has $x(\delta(\emptyset)) = 0 < 2$, so
including it would make the hypothesis unsatisfiable. -/
theorem proposition_1_rci {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ) (hQ : 0 < Q)
    (hq : ∀ i : Fin (n + 1), i ≠ 0 → 0 < q i ∧ (q i : ℝ) ≤ Q)
    (x : Sym2 (Fin (n + 1)) → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin (n + 1))) (hS0 : (0 : Fin (n + 1)) ∉ S) (hS : cut x S ≤ 2)
    (hR : ∀ R : Finset (Fin (n + 1)), R ⊆ S → R.Nonempty → R ≠ S → 2 ≤ cut x R) :
    SafeToShrink x (roundedCapacityBound q Q) S := by sorry

end LysgaardCVRP.Shrink
