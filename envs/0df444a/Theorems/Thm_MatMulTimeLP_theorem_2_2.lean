-- Prove2me | Theorems.Thm_MatMulTimeLP_theorem_2_2
-- name    : MatMulTimeLP.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:50:32.573695+00:00
-- url     : https://prove2.me/theorems/c516cdd2-d5e2-436c-ad5e-8051a46081dc
-- title:
--   Theorem 2.2 — the fix point algorithm, expected time $O(n^2\log^4 n)$
-- statement:
--   Let $f(t)=\sqrt{t^2+4}-2$, and consider the fix point equation $a=Hf(a)+h$, with $H\in\mathbb R^{n\times n}$, $h\in\mathbb R^n$. Suppose $\|H\|_2\le 1$, $\|h\|_2\le n$, and the equation has a solution with $\|a\|_1\le n$. Then there is a randomized algorithm that finds $\hat a\in\mathbb R^n$ with
--
--   $$\|Hf(\hat a)+h-\hat a\|_2\le n^{-5},\qquad\|\hat a\|_2\le 512n,$$
--
--   in expected time $O(n^2\log^4 n)$.
--
--   This is the paper's main technical theorem. Each round of the interior point method needs one call, and the bound has no $\omega$.
--
--   **Formalization Note** Programs of the real RAM, reading $H$ row by row and then $h$. `Measurable` is in the conclusion because `∫⁻` is a lower integral. Correctness holds on every halting run: the algorithm verifies its output before it returns (p.38).
--
--   Differences from the source:
--   - generalization: "has a unique solution $a$ satisfying $\|a\|_1\le n$" → "has a solution with $\|a\|_1\le n$"; reason: uniqueness is automatic from $|f'|<1$ and $\|H\|_2\le 1$ (p.19), and under either reading of "unique" the page's hypothesis implies this one
--   - reading: $O(n^2\log^4 n)$ → `∃ C, ∀ n ≥ 2`; reason: at $n=1$, $\log 1=0$ makes any $C\cdot 0$ bound false, so $n=1$ is out of the scope of the asymptotic; all $2\le n<100$ stay in
--   - reading: "a randomized algorithm" → a program for each $n$; reason: the mission's machine has no real-to-index conversion, and the size is not in the input; the family is the form that composes with `theorem_1_1`
--   - encoding: exact real arithmetic with Gaussian sampling → the deep randomized real RAM, every instruction costing $1$, with a uniform draw as well; reason: Section 3, p.15; Algorithms 5, 6 draw uniforms and make weighted choices
--   - encoding: "in expected time" → `Measurable` of the running time together with the `∫⁻` bound; reason: `∫⁻` is a lower integral, so measurability keeps the bound honest; the running time of every program is measurable (each step reads finitely many tape coordinates and branches on comparisons), so the clause excludes no algorithm
--   - reading: "finds a point $\hat a$ satisfying …" → the output of **every** halting run satisfies the conclusions; reason: the algorithm verifies before it returns (proof of Theorem 2.2, pp.38–39), so a returned point is always correct
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Theorem 2.2, p.7; proof, Section 5.4.4, pp.38–39

import Mathlib
import Definitions.Def_MatMulTimeLP_FixPoint

open scoped Matrix.Norms.L2Operator ENNReal

namespace MatMulTimeLP

open MeasureTheory

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Theorem 2.2, p.7 (proved in Section 5.4.4, pp.38–39): if
`‖H‖₂ ≤ 1`, `‖h‖₂ ≤ n` and `a = Hf(a) + h` has a solution with `‖a‖₁ ≤ n`, a randomized algorithm finds `â` with
`‖Hf(â) + h - â‖₂ ≤ n⁻⁵`, `‖â‖₂ ≤ 512n`, in expected time `O(n² log⁴ n)`.

**Formalization Note** Programs of the real RAM, one per size, reading `H` row by row, then `h`. Every instruction
costs `1`. `∫⁻` is a lower integral, hence `Measurable` in the conclusion. Correctness is on every halting run: the
algorithm verifies its output before returning (p.38). `O(·)` is `∃ C, ∀ n ≥ 2`, as `log 1 = 0`. The page's uniqueness
is automatic (p.19), so it is not assumed. -/
theorem theorem_2_2 :
    ∃ (alg : ℕ → Program) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ),
        ‖H‖ ≤ 1 → l2Norm h ≤ n → (∃ a, IsFixPoint H h a ∧ l1Norm a ≤ n) →
        (Measurable fun ω => (haltTime (alg n) (fixInput H h) ω : ℝ≥0∞)) ∧
        ∫⁻ ω, (haltTime (alg n) (fixInput H h) ω : ℝ≥0∞) ∂tapeLaw ≤
          ENNReal.ofReal (C * (n : ℝ) ^ 2 * Real.log n ^ 4) ∧
        ∀ (ω : Tape) (t : ℕ), HaltsAt (alg n) (fixInput H h) ω t →
          l2Norm (residual H h (outputAt (alg n) (fixInput H h) ω t n)) ≤ 1 / (n : ℝ) ^ 5 ∧
          l2Norm (outputAt (alg n) (fixInput H h) ω t n) ≤ 512 * n := by sorry

end MatMulTimeLP
