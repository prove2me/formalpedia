-- Prove2me | Theorems.Thm_MIQPInNP_SmallSol_claim_2
-- name    : MIQPInNP.SmallSol.claim_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:40.535594+00:00
-- url     : https://prove2.me/theorems/82c356eb-2239-4e2b-8db2-298c0cfd22a2
-- title:
--   Claim 2, p. 8 (restated with its context) — the solutions of (12) have Euclidean norm at most a rational v* of small complexity
-- statement:
--   This is Claim 2 of the proof of Theorem 1, restated with the objects of its context as hypotheses.
--
--   Let $P = \{x : A'x\le b'\}\subseteq\mathbb R^n$ be a rational polytope, let $r^1,\dots,r^k\in\mathbb Q^n$ be linearly independent, and let $H\in\mathbb Q^{n\times n}$, $c\in\mathbb Q^n$, $d\in\mathbb Q$. Put $J = \{j : (r^j)^\top Hr^j = 0\}$, $F_J = \operatorname{cone}(r^j)_{j\notin J}$ and $F^I_J = \operatorname{int.cone}(r^j)_{j\notin J}$, and assume
--   $$r^\top Hr>0\quad\text{for every nonzero } r\in F_J .$$
--   There is a single polynomial $g$, fixed before $n$, the number of rows of $A'$, $k$, and the data, such that there is a rational number $v^*$ with
--   $\operatorname{size}(v^*)\le g\big(\operatorname{size}(A')+\operatorname{size}(b')+\sum_j\operatorname{size}(r^j)+\operatorname{size}(H)+\operatorname{size}(c)+\operatorname{size}(d)\big)$
--   and, for every $x$ satisfying (12),
--   $$x^\top Hx + c^\top x + d\le 0,\quad x\in P+F^I_J\qquad\Longrightarrow\qquad \|x\|\le v^* ,$$
--   where $\|\cdot\|$ is the Euclidean norm.
--
--   The bound lets the proof of Theorem 1 fix the integer coordinates of a solution of (12) to values of small size and finish with Theorem 3.
--
--   **Formalization Note** The positivity hypothesis is the first sentence of the claim's proof (p. 8), which derives it from the conclusion of Lemma 7 and the definition of $J$; the page prints it "for all $r\in F_J$", which fails at $r=0$, so it is stated for nonzero $r$.
--
--   Differences from the source:
--   - generalization: the context of pp. 7–8 ($P=P_{\bar i}$, the $r^j$ from Lemma 7, Case 2 and the definition of $J$, "$\mathcal F$-small complexity") → any rational polytope, any linearly independent rational $r^j$ with $r^\top Hr>0$ on $F_J\setminus\{0\}$, bound polynomial in the sizes of the local data; reason: the source derives the positivity from its context in the first line of the proof, and its local data are $\mathcal F$-small, so the statement specializes to the source's claim.
--   - encoding: $\|x\|$ → Euclidean norm `euclidNorm`; reason: Lean's default norm on `Fin n → ℝ` is the sup norm, and the proof uses $\|\bar p\|\le\sqrt n\cdot v_4^*$.
-- source:
--   Del Pia, Dey & Molinaro, Mixed-integer quadratic programming is in NP, arXiv:1407.4798v1, p. 8, Claim 2 and Equation (12) (context pp. 7–8)

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

namespace MIQPInNP.SmallSol

open scoped Pointwise

/-- Claim 2, p. 8, restated with its context (Del Pia, Dey & Molinaro, arXiv:1407.4798v1). -/
theorem claim_2 :
    ∃ g : Polynomial ℕ, ∀ (n mP k : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ) (b' : Fin mP → ℚ)
      (r : Fin k → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ),
      Bornology.IsBounded (polyhedron A' b') →
      LinearIndependent ℝ (fun j => toReal (r j)) →
      (∀ x ∈ cone ((fun j => toReal (r j)) '' {j | quadForm H (toReal (r j)) ≠ 0}),
          x ≠ 0 → 0 < quadForm H x) →
      ∃ v : ℚ,
        bitSize v ≤ g.eval (matSize A' + vecSize b' + ∑ j, vecSize (r j) + matSize H + vecSize c
          + bitSize d) ∧
        ∀ x ∈ polyhedron A' b' + intCone ((fun j => toReal (r j)) '' {j | quadForm H (toReal (r j)) ≠ 0}),
          quadVal H c d x ≤ 0 → euclidNorm x ≤ v := by sorry

end MIQPInNP.SmallSol
