-- Prove2me | Theorems.Thm_MatMulTimeLP_theorem_1_1
-- name    : MatMulTimeLP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:59.173195+00:00
-- url     : https://prove2.me/theorems/ab428dde-1b26-46d4-9de5-0f99310ca9eb
-- title:
--   Theorem 1.1 (corrected: $\log(2+RW/\varepsilon)$) — every bounded LP in expected time $n^{\omega+o(1)}\log(2+RW/\varepsilon)$
-- statement:
--   Let $A\in\mathbb R^{d\times n}$ have full row rank, $b\in\mathbb R^d$, $c\in\mathbb R^n$. Suppose $\{x\ge 0:Ax=b\}$ is nonempty and every feasible point satisfies $\|x\|_\infty\le R$. Let $W=\max\{\max_{i,j}|A_{ij}|,\max_i|b_i|,\max_j|c_j|\}$. Then for every $\varepsilon>0$ a randomized algorithm returns $x\ge 0$ with
--
--   $$c^\top x\le\min_{x'\ge 0:\,Ax'=b}c^\top x'+\varepsilon,\qquad\|Ax-b\|_1\le\varepsilon,$$
--
--   in expected time
--
--   $$n^{\omega+o(1)}\log\Bigl(2+\frac{RW}\varepsilon\Bigr).$$
--
--   General linear programs can therefore be solved in the time of matrix multiplication, up to $n^{o(1)}$ and the logarithmic accuracy factor. This closes the gap left by the additive $n^{2+1/18}$ term of earlier algorithms.
--
--   **Formalization Note** The algorithm is a family of programs of a deep-embedded randomized real RAM, with no floor, in which every instruction costs $1$, including reads of the input. $\omega$ is `OAI.MatrixMultiplication.Arithmetic.omega ℝ`, from the source the paper cites. `Measurable` is in the conclusion because `∫⁻` is a lower integral. Correctness holds on every halting run, and finite expected time gives almost sure halting.
--
--   Differences from the source:
--   - correction: $\log(RW/\varepsilon)$ → $\log(2+RW/\varepsilon)$; reason: the printed bound is false: at $d=n=1$, $A=(1)$, $b=(1)$, $c=(0)$, $R=1$, $W=1$, $\varepsilon=1$ every assumption holds and the bound is $0$, negative for $\varepsilon>1$, while every run takes at least one step; restricting to $\varepsilon<RW$ does not help, since the factor tends to $0$ as $\varepsilon\uparrow RW$ for fixed $n$. The corrected form follows from Theorem 4.1, and footnote 1, p.3, treats the factor as polylog$(RW/\varepsilon)$
--   - reading: $n^{\omega+o(1)}$ → one $g\to 0$ and one constant $C$, chosen before the instance, with bound $Cn^{\omega+g(n)}\log(2+RW/\varepsilon)$ for every $n\ge 1$; reason: the $o(1)$ cannot depend on the instance; the constant is needed only because $1^x=1$ at $n=1$
--   - reading: "a randomized algorithm" → a per-size family `alg d n` of machine programs; reason: the paper cites a non-uniform $\omega$ ([Ope26]), one straight-line program per size, and a single uniform program is not derivable from it
--   - reading: the bound $R$ → $R$ is an input of the program; $R=0$ is allowed; reason: Theorem 4.1, p.15, the "slightly more detailed version of Theorem 1.1", says "a bound $R>0$ is given"
--   - generalization: "for every $\varepsilon$, there is a randomized algorithm" → one program for all $\varepsilon>0$, with $\varepsilon$ among its inputs; reason: fixing $\varepsilon$ in the input gives an algorithm for that $\varepsilon$, so the page's statement is an instance; $\varepsilon>0$ is implicit (the page divides by $\varepsilon$)
--   - encoding: exact real arithmetic with Gaussian sampling, in unit cost → the deep randomized real RAM of `MatMulTimeLP.RealRAM`, with a uniform draw as well; reason: Section 3, p.15; Algorithms 5, 6 draw uniforms
--   - encoding: $\min_{x'\ge 0:Ax'=b}c^\top x'$; "full row rank"; $W$ → `∀ x'` feasible; `A.rank = d`; a maximum of sup norms; reason: the feasible set is nonempty and compact; same meaning; same value
--   - encoding: "in expected time" → `Measurable` of the running time together with the `∫⁻` bound; reason: `∫⁻` is a lower integral, so measurability keeps the bound honest; the running time of every program is measurable (each step reads finitely many tape coordinates and branches on comparisons), so the clause excludes no algorithm
--   - reading: "returns $x$ satisfying …" → the output of **every** halting run satisfies the conclusions; reason: the algorithm verifies before it returns (proof of Theorem 2.2, pp.38–39), so a returned point is always correct
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_MatMulTimeLP_LP
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

open scoped ENNReal

namespace MatMulTimeLP

open Matrix MeasureTheory Filter Topology WrightPDIPM.CentralPath

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Theorem 1.1, p.3 (corrected): for `A` of full row rank, a nonempty
feasible region inside the box `‖x‖_∞ ≤ R`, and `W` the largest absolute entry of `A, b, c`, a randomized algorithm
returns `x ≥ 0` with `cᵀx ≤ min cᵀx' + ε` and `‖Ax - b‖₁ ≤ ε` in expected time `n^(ω+o(1)) log(2 + RW/ε)`.

**Formalization Note** The algorithm is a family of programs of the deep randomized real RAM (`Program`), one per size
`(d, n)`, with `g → 0` and `C` before the instance, because the published `ω` (`omega ℝ`, the paper's source [Ope26])
is non-uniform. `R`, `ε` are inputs, read with `A, b, c`. Every instruction costs `1`; there is no floor. `∫⁻` is a
lower integral, hence `Measurable`. Correctness holds on every halting run, and finite expected time gives almost sure
halting. The printed factor `log(RW/ε)` is `≤ 0` for `ε ≥ RW`, so it is corrected to `log(2 + RW/ε)`. -/
theorem theorem_1_1 :
    ∃ (alg : ℕ → ℕ → Program) (g : ℕ → ℝ) (C : ℝ), Tendsto g atTop (𝓝 0) ∧ 0 < C ∧
      ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ) (c : Fin n → ℝ) (R ε : ℝ),
        1 ≤ n → A.rank = d → (∃ x, PrimalFeasible A b x) →
        (∀ x, PrimalFeasible A b x → ∀ j, |x j| ≤ R) → 0 < ε →
        (Measurable fun ω => (haltTime (alg d n) (lpInput A b c R ε) ω : ℝ≥0∞)) ∧
        ∫⁻ ω, (haltTime (alg d n) (lpInput A b c R ε) ω : ℝ≥0∞) ∂tapeLaw ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ + g n) *
            Real.log (2 + R * lpWidth A b c / ε)) ∧
        ∀ (ω : Tape) (t : ℕ), HaltsAt (alg d n) (lpInput A b c R ε) ω t →
          let x := outputAt (alg d n) (lpInput A b c R ε) ω t n
          (∀ j, 0 ≤ x j) ∧
          (∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x' + ε) ∧
          l1Norm (A *ᵥ x - b) ≤ ε := by sorry

end MatMulTimeLP
