-- Prove2me | Theorems.Thm_MIQPInNP_SmallSol_theorem_3
-- name    : MIQPInNP.SmallSol.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:39.853798+00:00
-- url     : https://prove2.me/theorems/ee91f969-bd87-40ad-b522-7ff6eb98fceb
-- title:
--   Theorem 3, p. 3 — QP feasibility has small certificates, and a QP with a global optimum has an optimal solution of small bit-size (Vavasis)
-- statement:
--   This is Vavasis's theorem that quadratic programming is in NP, as used by Del Pia, Dey and Molinaro.
--
--   For $H\in\mathbb Q^{n\times n}$, $c\in\mathbb Q^n$, $d\in\mathbb Q$, $A\in\mathbb Q^{m\times n}$ and $b\in\mathbb Q^m$, write $\varphi = \operatorname{size}\{H,c,d,A,b\}$ for the total bit-size of the data. There is a single polynomial $g$ with natural coefficients, fixed before $n$, $m$ and the data, such that:
--
--   1. **Feasibility (continuous relaxation of (2)).** If the real set $\{x\in\mathbb R^n : x^\top Hx + c^\top x + d\le 0,\ Ax\le b\}$ is non-empty, it contains a rational point $\hat x$ with $\operatorname{size}(\hat x)\le g(\varphi)$.
--   2. **Optimization (continuous relaxation of (1)).** If the quadratic program
--   $$\min\{x^\top H x + c^\top x : Ax\le b,\ x\in\mathbb R^n\}$$
--   has a global optimal solution, then it has a rational global optimal solution $\hat x$ with $\operatorname{size}(\hat x)\le g(\varphi)$.
--
--   The second part is the form in which the proof of Theorem 1 uses the result (pp. 6–9): optimal solutions of auxiliary quadratic programs over sets of small complexity have small complexity.
--
--   **Formalization Note** "Is in NP" is rendered as the existence of polynomial-size certificates, since Mathlib has no complexity class NP; checking a rational certificate is routine. The polynomial is a `Polynomial ℕ` quantified before every dimension and every datum: a bound chosen after the data would make the statement trivially true.
--
--   Differences from the source:
--   - reading: "the feasibility problem over the continuous relaxation of (2) is in NP" → every feasible instance has a rational feasible point of bit-size at most $g(\varphi)$; reason: Mathlib has no class NP, and a polynomial-size certificate is the content of the claim (the paper's own justification of Proposition 5, p. 5, reads "in NP" the same way).
--   - reading: "there exists a system of rational linear equations of $\{H,c,d,A,b\}$-small complexity whose solution is one of the global optimal solutions" → there is a global optimal solution of bit-size at most $g(\varphi)$; reason: equivalent statements (by Cramer's rule the solution of a linear system of size $s$ has size polynomial in $s$; conversely $\hat x$ is the solution of the system $x=\hat x$), and this is the form the proof uses on pp. 6–9.
--   - generalization: (1) assumes $H$ symmetric → any rational $H$; reason: $x^\top Hx$ depends only on $(H+H^\top)/2$, whose size is polynomial in that of $H$, so the statement specializes to the symmetric case.
--   - encoding: "polynomial" and "complexity" → `Polynomial ℕ` evaluated at Schrijver's bit-size; reason: every standard encoding and every real polynomial bound is polynomially equivalent to these.
-- source:
--   Del Pia, Dey & Molinaro, Mixed-integer quadratic programming is in NP, arXiv:1407.4798v1, p. 3, Theorem 3

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

namespace MIQPInNP.SmallSol

/-- Theorem 3, p. 3 (Del Pia, Dey & Molinaro, arXiv:1407.4798v1). -/
theorem theorem_3 :
    ∃ g : Polynomial ℕ,
      (∀ (n m : ℕ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
        (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        (feasSet 0 H c d A b).Nonempty →
        ∃ xh : Fin n → ℚ, toReal xh ∈ feasSet 0 H c d A b ∧
          vecSize xh ≤ g.eval (instSize H c d A b)) ∧
      (∀ (n m : ℕ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
        (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        (∃ x ∈ polyhedron A b, ∀ y ∈ polyhedron A b, quadVal H c 0 x ≤ quadVal H c 0 y) →
        ∃ xh : Fin n → ℚ, toReal xh ∈ polyhedron A b ∧
          (∀ y ∈ polyhedron A b, quadVal H c 0 (toReal xh) ≤ quadVal H c 0 y) ∧
          vecSize xh ≤ g.eval (instSize H c d A b)) := by sorry

end MIQPInNP.SmallSol
