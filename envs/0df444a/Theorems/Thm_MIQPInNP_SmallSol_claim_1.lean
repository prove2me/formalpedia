-- Prove2me | Theorems.Thm_MIQPInNP_SmallSol_claim_1
-- name    : MIQPInNP.SmallSol.claim_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:43.991239+00:00
-- url     : https://prove2.me/theorems/ae11a559-7351-4990-9136-f5645414b642
-- title:
--   Claim 1, p. 7 (restated with its context) — a negative linear objective on P + F^I_i is attained at a point of small complexity
-- statement:
--   This is Claim 1 of the proof of Theorem 1, restated with the objects of its context as hypotheses.
--
--   Let $P = \{x : A'x\le b'\}\subseteq\mathbb R^n$ be a rational polytope, let $r^1,\dots,r^k\in\mathbb Q^n$ be linearly independent (the rays of a simple cone), let $H\in\mathbb Q^{n\times n}$ and $c\in\mathbb Q^n$, and let $i$ be an index with $(r^i)^\top Hr^i = 0$ (that is, $i\in J$). Put $F^I_i = \operatorname{int.cone}(r^j)_{j\neq i}$ and
--   $$\mathrm{obj}(x) = 2x^\top Hr^i + c^\top r^i .$$
--   There is a single polynomial $g$, fixed before $n$, the number of rows of $A'$, $k$, and the data, such that: if $\mathrm{obj}$ takes a negative value somewhere on $P + F^I_i$, then there is a rational point $\tilde x^i\in P+F^I_i$ with $\mathrm{obj}(\tilde x^i)<0$ and
--   $$\operatorname{size}(\tilde x^i)\ \le\ g\big(\operatorname{size}(A')+\operatorname{size}(b')+\textstyle\sum_j\operatorname{size}(r^j)+\operatorname{size}(H)+\operatorname{size}(c)\big).$$
--
--   In the proof of Theorem 1 the point $\tilde x^i$ is then pushed along the direction $r^i$, on which $\mathcal Q$ is linear, to produce a feasible point of small complexity.
--
--   **Formalization Note** The objective is kept as printed, $2x^\top Hr^i$, without symmetrizing $H$.
--
--   Differences from the source:
--   - generalization: the context of p. 7 ($P=P_{\bar i}$ from Proposition 4, $r^j$ the rays of a cone from Lemma 7, "$\mathcal F$-small complexity") → any rational polytope, any linearly independent rational $r^j$, bound polynomial in the sizes of these local data; reason: in the source's context $P$, the $r^j$, $H$ and $c$ are themselves $\mathcal F$-small, so composing the polynomials gives the source's $\mathcal F$-small bound.
--   - reading: "the optimum of this problem is negative" → the objective takes a negative value somewhere on $P+F^I_i$; reason: the infimum is negative exactly when some point has a negative value.
-- source:
--   Del Pia, Dey & Molinaro, Mixed-integer quadratic programming is in NP, arXiv:1407.4798v1, p. 7, Claim 1 (context pp. 6–7)

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

namespace MIQPInNP.SmallSol

open scoped Pointwise

/-- Claim 1, p. 7, restated with its context (Del Pia, Dey & Molinaro, arXiv:1407.4798v1). -/
theorem claim_1 :
    ∃ g : Polynomial ℕ, ∀ (n mP k : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ) (b' : Fin mP → ℚ)
      (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (i : Fin k),
      Bornology.IsBounded (polyhedron A' b') →
      LinearIndependent ℝ (fun j => toReal (r j)) →
      quadForm H (toReal (r i)) = 0 →
      (∃ x ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | j ≠ i}),
          2 * (∑ u, ∑ v, x u * (H u v : ℝ) * toReal (r i) v) + ∑ u, (c u : ℝ) * toReal (r i) u
            < 0) →
      ∃ xt : Fin n → ℚ,
        toReal xt ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | j ≠ i}) ∧
        2 * (∑ u, ∑ v, toReal xt u * (H u v : ℝ) * toReal (r i) v)
            + ∑ u, (c u : ℝ) * toReal (r i) u < 0 ∧
        vecSize xt ≤ g.eval (matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c) := by sorry

end MIQPInNP.SmallSol
