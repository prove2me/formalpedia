-- Prove2me | Theorems.Thm_MatMulTimeLP_theorem_4_1
-- name    : MatMulTimeLP.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:55.385886+00:00
-- url     : https://prove2.me/theorems/40f47465-965e-4f91-9bef-43b95eba0822
-- title:
--   Theorem 4.1 — the detailed main theorem, $n\ge 100$, $0<\varepsilon<1$
-- statement:
--   Let $A\in\mathbb R^{d\times n}$, $b$, $c$, with $n\ge 100$. Suppose $A$ has full row rank, that $\{x\ge 0:Ax=b\}$ is nonempty, and that a bound $R>0$ is given such that every feasible point satisfies $\|x\|_\infty\le R$. Then for every $0<\varepsilon<1$ there is a randomized algorithm that returns $\hat x\ge 0$ with
--
--   $$c^\top\hat x\le\min_{Ax=b,\,x\ge 0}c^\top x+\varepsilon R\|c\|_\infty,\qquad\|A\hat x-b\|_1\le\varepsilon\Bigl(R\sum_{i,j}|A_{ij}|+\|b\|_1\Bigr),$$
--
--   in expected time
--
--   $$O\Bigl((d+n)^{\omega+o(1)}\log\frac n\varepsilon+n^2\log^4 n\log\frac n\varepsilon\Bigr).$$
--
--   This form keeps the two costs of a round apart, one matrix inverse and one fix point solve.
--
--   **Formalization Note** See `theorem_1_1` for the model. $g$ and $C$ are chosen before the instance.
--
--   Differences from the source:
--   - reading: $O((d+n)^{\omega+o(1)}\log(n/\varepsilon)+\dots)$ and "a randomized algorithm" → one family `alg d n`, one $g\to 0$ and one $C$, chosen before the instance; reason: the published $\omega$ is non-uniform, one program per size, and that is what allows a single $o(1)$
--   - generalization: "for every $0<\varepsilon<1$, there is a randomized algorithm" → one program for all $\varepsilon$, with $R$ and $\varepsilon$ among its inputs; reason: p.15 says "a bound $R>0$ is given"; fixing $\varepsilon$ in the input gives an algorithm for that $\varepsilon$, so the page's statement is an instance, and the proof gives the uniform program
--   - encoding: exact real arithmetic; $\min$; "full row rank" → the deep randomized real RAM; `∀ x'` feasible; `A.rank = d`; reason: Section 3, p.15; the feasible set is nonempty and compact; same meaning
--   - encoding: "in expected time" → `Measurable` of the running time together with the `∫⁻` bound; reason: `∫⁻` is a lower integral, so measurability keeps the bound honest; the running time of every program is measurable (each step reads finitely many tape coordinates and branches on comparisons), so the clause excludes no algorithm
--   - reading: "returns $\hat x$ satisfying …" → the output of **every** halting run satisfies the conclusions; reason: the algorithm verifies before it returns (proof of Theorem 2.2, pp.38–39), so a returned point is always correct
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Theorem 4.1, pp.15–16

import Mathlib
import Definitions.Def_MatMulTimeLP_LP
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

open scoped ENNReal

namespace MatMulTimeLP

open Matrix MeasureTheory Filter Topology WrightPDIPM.CentralPath

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Theorem 4.1, pp.15–16: for `n ≥ 100`, `A` of full row rank, a
nonempty feasible region, a given bound `R > 0` and `0 < ε < 1`, a randomized algorithm returns `x̂ ≥ 0` with
`cᵀx̂ ≤ min cᵀx + εR‖c‖_∞` and `‖Ax̂ - b‖₁ ≤ ε(R∑|A_ij| + ‖b‖₁)` in expected time
`O((d+n)^(ω+o(1)) log(n/ε) + n² log⁴ n log(n/ε))`.

**Formalization Note** A per-size family of real-RAM programs, with one `g → 0` and one `C` chosen before the instance;
`R`, `ε` are inputs. See `theorem_1_1` for the model. Correctness holds on every halting run. -/
theorem theorem_4_1 :
    ∃ (alg : ℕ → ℕ → Program) (g : ℕ → ℝ) (C : ℝ), Tendsto g atTop (𝓝 0) ∧ 0 < C ∧
      ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ) (R ε : ℝ),
        100 ≤ n → A.rank = d → (∃ x, PrimalFeasible A b x) → 0 < R →
        (∀ x, PrimalFeasible A b x → ∀ j, |x j| ≤ R) → 0 < ε → ε < 1 →
        (Measurable fun ω => (haltTime (alg d n) (lpInput A b c R ε) ω : ℝ≥0∞)) ∧
        ∫⁻ ω, (haltTime (alg d n) (lpInput A b c R ε) ω : ℝ≥0∞) ∂tapeLaw ≤
          ENNReal.ofReal (C *
            (((d : ℝ) + n) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ + g (d + n)) *
                Real.log ((n : ℝ) / ε) +
              (n : ℝ) ^ 2 * Real.log n ^ 4 * Real.log ((n : ℝ) / ε))) ∧
        ∀ (ω : Tape) (t : ℕ), HaltsAt (alg d n) (lpInput A b c R ε) ω t →
          let x := outputAt (alg d n) (lpInput A b c R ε) ω t n
          (∀ j, 0 ≤ x j) ∧
          (∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x' + ε * R * ‖c‖) ∧
          l1Norm (A *ᵥ x - b) ≤ ε * (R * ∑ i, ∑ j, |A i j| + l1Norm b) := by sorry

end MatMulTimeLP
