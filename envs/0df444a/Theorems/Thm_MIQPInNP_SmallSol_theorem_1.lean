-- Prove2me | Theorems.Thm_MIQPInNP_SmallSol_theorem_1
-- name    : MIQPInNP.SmallSol.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:58.662473+00:00
-- url     : https://prove2.me/theorems/4487e2b7-432f-4a9b-ace6-b0ad6a98e6ac
-- title:
--   Theorem 1, p. 2 — a non-empty mixed-integer quadratic feasible set contains a rational point of polynomial bit-size
-- statement:
--   Let $n,p$ be positive integers with $p\le n$, let $m\ge0$, and let $H\in\mathbb Q^{n\times n}$, $c\in\mathbb Q^n$, $d\in\mathbb Q$, $A\in\mathbb Q^{m\times n}$, $b\in\mathbb Q^m$. Let $\varphi$ be the complexity (total bit-size) of $\{H,c,d,A,b\}$ and let
--   $$\mathcal F(H,c,d,A,b) = \{x\in\mathbb R^n : x^\top Hx + c^\top x + d\le 0,\ Ax\le b,\ x\in\mathbb Z^p\times\mathbb R^{n-p}\}.$$
--   There is a single polynomial $f$, fixed before $n$, $p$, $m$ and the data, such that: if $\mathcal F(H,c,d,A,b)$ is non-empty, then it contains a rational point $x^0$ with
--   $$\operatorname{size}(x^0)\le f(\varphi).$$
--
--   Such an $x^0$ is a polynomial-length certificate for yes-instances of decision MIQP, so the decision versions of integer and mixed-integer quadratic programming are in NP (Corollary 2 of the paper). The result generalizes the classical facts that quadratic programming (Vavasis) and integer linear programming are in NP.
--
--   **Formalization Note** Non-emptiness is assumed over the reals (the first $p$ coordinates integral), and the conclusion asks for a rational point whose first $p$ coordinates are integers. $H$ need not be symmetric, as in the theorem. The polynomial is a `Polynomial ℕ` quantified before all dimensions and data; a polynomial chosen after the instance would make the statement trivial.
--
--   Differences from the source:
--   - reading: "$f$ is a polynomial function" → one polynomial $f$ quantified before $n$, $p$, $m$ and the data; reason: an instance-dependent bound is trivially true, and the paper's definition of $\mathcal O$-small complexity (§2.1, p. 3: "there is a polynomial $p$ such that for every input object") fixes this order.
--   - encoding: $x\in\mathbb Z^p\times\mathbb R^{n-p}$ with $n,p\in\mathbb Z_{++}$ → hypotheses $0<n$, $0<p$, $p\le n$; reason: $p\le n$ is implicit in $\mathbb R^{n-p}$.
--   - encoding: "complexity" and "polynomial" → Schrijver's bit-size and `Polynomial ℕ`; reason: polynomially equivalent to any standard binary encoding and any polynomial bound.
-- source:
--   Del Pia, Dey & Molinaro, Mixed-integer quadratic programming is in NP, arXiv:1407.4798v1, p. 2, Theorem 1 (with Equation (2), p. 1)

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

namespace MIQPInNP.SmallSol

/-- Theorem 1, p. 2 (Del Pia, Dey & Molinaro, arXiv:1407.4798v1). -/
theorem theorem_1 :
    ∃ f : Polynomial ℕ, ∀ (n p m : ℕ), 0 < n → 0 < p → p ≤ n →
      ∀ (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
        (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        (feasSet p H c d A b).Nonempty →
        ∃ x0 : Fin n → ℚ, toReal x0 ∈ feasSet p H c d A b ∧
          vecSize x0 ≤ f.eval (instSize H c d A b) := by sorry

end MIQPInNP.SmallSol
