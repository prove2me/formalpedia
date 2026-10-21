-- Prove2me | Theorems.Thm_ModernConvex_LPDuality_lp_duality_theorem
-- name    : ModernConvex.LPDuality.lp_duality_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:26.159493+00:00
-- url     : https://prove2.me/theorems/31245a35-217d-4cb4-a313-8e05ce8e3aaf
-- title:
--   Theorem 1.3.2 — duality theorem in linear programming: symmetry, weak duality, and the equivalence of (i)–(v) with equal optimal values
-- statement:
--   Let $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$, and consider the LP program
--   $$\text{(LP)}\qquad \min_x\left\{c^Tx \;\middle|\; Ax \ge b\right\}$$
--   along with its dual
--   $$\text{(LP}^*)\qquad \max_y\left\{b^Ty \;\middle|\; A^Ty = c,\ y \ge 0\right\}.$$
--   Then:
--
--   1. **The duality is symmetric**: the problem dual to the dual is equivalent to the primal. Precisely, (LP$^*$) is the program $\min_y\{-b^Ty \mid A'y \ge b'\}$ in the form (LP), with $A' = [I_m;\ A^T;\ -A^T]$ and $b' = (0;\ c;\ -c)$ — its feasible set is exactly that of (LP$^*$). The dual of this program is $\max\{b'^Tw \mid A'^Tw = -b,\ w \ge 0\}$ in $w = (\xi, \eta, \zeta) \in \mathbb R^m \times \mathbb R^n \times \mathbb R^n$, i.e. $\max\{c^T\eta - c^T\zeta \mid \xi + A\eta - A\zeta = -b,\ \xi, \eta, \zeta \ge 0\}$; the map $w \mapsto x = \zeta - \eta$ sends its feasible points to feasible points of (LP), with $b'^Tw = -c^Tx$, and every feasible $x$ of (LP) arises in this way.
--   2. The value of the dual objective at every dual feasible solution is $\le$ the value of the primal objective at every primal feasible solution: $b^Ty \le c^Tx$ whenever $Ax \ge b$, $A^Ty = c$, $y \ge 0$.
--   3. The following properties are equivalent to each other:
--      - (i) the primal is feasible and bounded below,
--      - (ii) the dual is feasible and bounded above,
--      - (iii) the primal is solvable,
--      - (iv) the dual is solvable,
--      - (v) both primal and dual are feasible.
--
--      Whenever (i) $\equiv$ (ii) $\equiv$ (iii) $\equiv$ (iv) $\equiv$ (v) is the case, the optimal values of the primal and the dual problems are equal to each other: there is a real $v$ with
--   $$v = \inf\{c^Tx \mid Ax \ge b\} = \sup\{b^Ty \mid A^Ty = c,\ y \ge 0\}.$$
--
--   This is the LP duality theorem in the inequality form used throughout the book; the conic duality theorem of Lecture 2 extends it from the nonnegative orthant to general cones.
--
--   **Formalization Note** Item 1 is informal in the book ("equivalent"); it is formalized by the rewriting carried out in the book's proof (p. 18): the first clause checks the rewriting of (LP$^*$) into the form (LP), and the second and third clauses say that $x = \zeta - \eta$ maps the feasible set of the dual of (LP$^*$) onto the feasible set of (LP), with objective $-c^Tx$, so that maximizing it is minimizing $c^Tx$. The book's display writes the dual of (LP$^*$) with the constraint $\xi - A\eta + A\zeta = -b$ and $x = \eta - \zeta$; the signs are interchanged there (see FINDINGS.yaml F2), and the Lean states the correct computation. "Bounded below/above", "solvable" and "optimal value" are the explicit predicates of `ModernConvex.LPDuality.LinearProgram`; the equality of optimal values is stated as one real $v$ that is both the greatest lower bound of the primal objective values and the least upper bound of the dual ones, so no junk value of an infimum enters. The equivalence of (i)–(v) is `List.TFAE`. No rank condition on $A$ is assumed (Assumption A belongs to Lecture 2).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 18, Theorem 1.3.2 (duality theorem in linear programming); item 1 made precise by the rewriting in its proof, p. 18

import Mathlib
import Definitions.Def_ModernConvex_LPDuality_LinearProgram

open Matrix

namespace ModernConvex.LPDuality

/-- Ben-Tal–Nemirovski, Theorem 1.3.2 (duality theorem in linear programming), p. 18, for
`(LP) : min { cᵀx | Ax ≥ b }` and `(LP∗) : max { bᵀy | Aᵀy = c, y ≥ 0 }`.
Item 1: `(LP∗)` is `min { −bᵀy | [I; Aᵀ; −Aᵀ] y ≥ (0; c; −c) }`; the dual of that program has
feasible points `(ξ, η, ζ)` mapped onto the feasible points of `(LP)` by `x = ζ − η`, with
objective value `−cᵀx`.
Item 2: weak duality.
Item 3: the five properties (i)–(v) are equivalent, and then the optimal values coincide. -/
theorem lp_duality_theorem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    -- 1. the duality is symmetric
    ((∀ y : Fin m → ℝ,
        PrimalFeasible (dualAsLPMatrix A) (dualAsLPRhs (m := Fin m) c) y ↔ DualFeasible A c y) ∧
      (∀ w : Fin m ⊕ (Fin n ⊕ Fin n) → ℝ, DualFeasible (dualAsLPMatrix A) (-b) w →
        PrimalFeasible A b (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))) ∧
        dualAsLPRhs c ⬝ᵥ w =
          -(c ⬝ᵥ (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))))) ∧
      (∀ x : Fin n → ℝ, PrimalFeasible A b x →
        ∃ w : Fin m ⊕ (Fin n ⊕ Fin n) → ℝ, DualFeasible (dualAsLPMatrix A) (-b) w ∧
          (fun j => w (Sum.inr (Sum.inr j)) - w (Sum.inr (Sum.inl j))) = x ∧
          dualAsLPRhs c ⬝ᵥ w = -(c ⬝ᵥ x))) ∧
    -- 2. weak duality
    (∀ (x : Fin n → ℝ) (y : Fin m → ℝ), PrimalFeasible A b x → DualFeasible A c y →
      b ⬝ᵥ y ≤ c ⬝ᵥ x) ∧
    -- 3. (i) ≡ (ii) ≡ (iii) ≡ (iv) ≡ (v)
    [PrimalIsFeasible A b ∧ PrimalBoundedBelow A b c,
      DualIsFeasible A c ∧ DualBoundedAbove A b c,
      PrimalSolvable A b c,
      DualSolvable A b c,
      PrimalIsFeasible A b ∧ DualIsFeasible A c].TFAE ∧
    -- ... and then the optimal values of the primal and the dual are equal
    (PrimalIsFeasible A b ∧ PrimalBoundedBelow A b c →
      ∃ v : ℝ, IsPrimalOptimalValue A b c v ∧ IsDualOptimalValue A b c v) := by sorry

end ModernConvex.LPDuality
