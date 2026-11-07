-- Prove2me | Theorems.Thm_MatMulTimeLP_theorem_5_10
-- name    : MatMulTimeLP.theorem_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:51:45.637618+00:00
-- url     : https://prove2.me/theorems/18a76cae-44e7-4fe0-83ed-39685aabf508
-- title:
--   Theorem 5.10 — convergence of Algorithm 3, and the bounds (10), (11)
-- statement:
--   Let $n\ge 1$, $\|H\|_2\le 1$, $\|h\|_2\le n$, let $a=Hf(a)+h$ with $\|a\|_1\le n$, and let $\Lambda=2^{24}n^2$. Let $C_k$ count the coordinate shrinkages of cleanup in iteration $k$, counting multiplicity. Then
--
--   $$\mathbb E[D_\Psi(a,z_{k+1})\mid z_k]\le\Bigl(1-\frac1{8\Lambda}\Bigr)D_\Psi(a,z_k)-\frac{\|r_k\|_2^2}{64\Lambda}-\frac1{100}\mathbb E[C_k\mid z_k].$$
--
--   Starting from $z_0=0$, after $L$ iterations,
--
--   $$\mathbb E[D_\Psi(a,z_L)]\le\frac n2e^{-L/(8\Lambda)},\qquad\mathbb E[\|r_L\|_2^2]\le 4n(2+320n)^2e^{-L/(8\Lambda)}.$$
--
--   For $L=\lceil 8\Lambda\log(64n^{11}(2+320n)^2)\rceil=O(n^2\log n)$ this gives $\mathbb E[\|r_L\|_2]\le n^{-5}/4$. Over the entire run,
--
--   $$\mathbb E\Bigl[\sum_{k<L}\frac{\|r_k\|_2^2}{\Lambda}\Bigr]\le 32n,\quad(10)\qquad\qquad\mathbb E\Bigl[\sum_{k<L}C_k\Bigr]\le 50n.\quad(11)$$
--
--   The bounds (10) and (11) are what the running-time analysis of the data structures rests on.
--
--   **Formalization Note** The theorem is about the ideal chain, which samples $i$ with the exact probability $w_i/\Lambda$. The asymptotic clause is `∃ C₀, ∀ n ≥ 2`.
--
--   Differences from the source:
--   - generalization: (10) and (11) for the paper's $L$ → at every horizon $L$; reason: the proof gives this, and the paper's $L$ is a special value
--   - reading: "using $O(n^2\log n)$ iterations" → `∃ C₀, ∀ n ≥ 2, L n ≤ C₀ n² log n`; reason: at $n=1$, $\log 1=0$, so $n=1$ is out of the scope of the asymptotic
--   - encoding: expectations over the run → the finite trees `stepExp`, `iterExp`, `runSum`; reason: the chain has finitely many outcomes per iteration, so no measure is needed
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Theorem 5.10, p.30

import Mathlib
import Definitions.Def_MatMulTimeLP_Chain

open scoped Matrix.Norms.L2Operator

namespace MatMulTimeLP

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Theorem 5.10, p.30, for Algorithm 3 with the exact sampling
probabilities: the one-step bound; `E[D_Ψ(a, z_L)] ≤ (n/2) e^{-L/(8Λ)}` and
`E[‖r_L‖₂²] ≤ 4n(2 + 320n)² e^{-L/(8Λ)}`; `E[‖r_L‖₂] ≤ n⁻⁵/4` at `L = ⌈8Λ log(64n¹¹(2 + 320n)²)⌉ = O(n² log n)`; and
(10) `E[∑_{k<L} ‖r_k‖₂²/Λ] ≤ 32n`, (11) `E[∑_{k<L} C_k] ≤ 50n`.

**Formalization Note** `stepExp`, `iterExp`, `runSum` are finite-tree expectations. The two exponential bounds and
(10), (11) hold at every horizon `L`, of which the paper's `L` is a special value. The asymptotic clause is
`∃ C₀, ∀ n ≥ 2`, as `log 1 = 0`. -/
theorem theorem_5_10 :
    (∃ C₀ : ℝ, ∀ n : ℕ, 2 ≤ n → (stepsL n : ℝ) ≤ C₀ * (n : ℝ) ^ 2 * Real.log n) ∧
    ∀ {n : ℕ} (_hn : 1 ≤ n) (H : Matrix (Fin n) (Fin n) ℝ) (h a : Fin n → ℝ)
      (_hH : ‖H‖ ≤ 1) (_hh : l2Norm h ≤ n) (_ha : IsFixPoint H h a) (_ha1 : l1Norm a ≤ n),
      (∀ z, Reachable H h z →
        stepExp H h z (fun o => bregPsi a o.1) ≤
          (1 - 1 / (8 * bigLam n)) * bregPsi a z -
            (∑ i, residual H h z i ^ 2) / (64 * bigLam n) -
            1 / 100 * stepExp H h z (fun o => (o.2 : ℝ))) ∧
      (∀ L : ℕ, iterExp H h L 0 (fun z => bregPsi a z) ≤
        (n : ℝ) / 2 * Real.exp (-((L : ℝ) / (8 * bigLam n)))) ∧
      (∀ L : ℕ, iterExp H h L 0 (fun z => ∑ i, residual H h z i ^ 2) ≤
        4 * (n : ℝ) * (2 + 320 * (n : ℝ)) ^ 2 * Real.exp (-((L : ℝ) / (8 * bigLam n)))) ∧
      iterExp H h (stepsL n) 0 (fun z => l2Norm (residual H h z)) ≤ 1 / (n : ℝ) ^ 5 / 4 ∧
      (∀ L : ℕ, runSum H h (fun z => (∑ i, residual H h z i ^ 2) / bigLam n) 0 L 0 ≤ 32 * n) ∧
      (∀ L : ℕ, runSum H h (fun _ => 0) 1 L 0 ≤ 50 * n) := by sorry

end MatMulTimeLP
