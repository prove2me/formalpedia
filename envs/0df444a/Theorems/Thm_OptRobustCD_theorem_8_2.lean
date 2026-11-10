-- Prove2me | Theorems.Thm_OptRobustCD_theorem_8_2
-- name    : OptRobustCD.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:50:56.540075+00:00
-- url     : https://prove2.me/theorems/03ab3b02-418e-4dc5-bcc7-8706567de6ae
-- title:
--   Theorem 8.2 — fast optimization: $\mathbb EF(ZZ^T)\le\min_{\mathcal S}F+\delta$ with $O((1+P/\delta)^5(\log n)^2)$ matrix-vector products
-- statement:
--   Let $n\ge2$. Given $K\ge1$, $0<\delta\le P$, a symmetric matrix $A\in\mathbb R^{n\times n}$ through a matrix-vector multiplication oracle, and a bound $P\ge\|A\|_{1,\infty}+1$, a randomized algorithm computes $Z\in\mathbb R^{n\times r}$ such that
--   $$ZZ^T\in\mathcal S,\qquad\mathbb EF(ZZ^T)\le\min_{\mathcal S}F+\delta,\qquad r\le O\bigl(1+P^4\log n/\delta^4\bigr),$$
--   where $F(X)=\langle A,X\rangle+P\cdot\mathrm{dist}_1(\mathrm{diag}X,\mathcal D_K)$. The algorithm uses $O((1+P/\delta)^5(\log n)^2)$ matrix-vector multiplications with $A$ and at most $n$ times as many additional operations.
--
--   It makes the convex program of Theorem 8.1 solvable in nearly-linear time (matrix multiplicative weights).
--
--   Differences from the source:
--   - reading: a randomized algorithm using O((1+P/δ)⁵(log n)²) products and at most n times as many other operations; r ⩽ O(1 + P⁴ log n/δ⁴) → one real-RAM program and one universal c₀, chosen before n, K, δ, P, A; input [n, K, δ, P], A only through the oracle; on every tape it halts within those counts (factor c₀) with output [r] ++ Z (row by row), ZZ^T ∈ S, r ⩽ c₀(1 + P⁴ log n/δ⁴); reason: the paper names no machine; O(·) is an absolute constant
--   - encoding: E F(ZZ^T) → the integral over the tape measure, with its integrability asserted; reason: the meaning of the expectation; integrability is asserted so that Lean's value 0 for non-integrable functions cannot make the bound trivial
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Theorem 8.2, p.37 (pdf p.39)

import Mathlib
import Definitions.Def_OptRobustCD_Machine
import Definitions.Def_OptRobustCD_RowNorms
import Definitions.Def_OptRobustCD_SDPObjective

open MeasureTheory

namespace OptRobustCD

/-- **Theorem 8.2** (Fast optimization). Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust
Community Detection*, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d54…),
Theorem 8.2, p.37 (pdf p.39).

"Given K ⩾ 1, 0 < δ ⩽ P, a symmetric matrix `A ∈ R^{n×n}` through a matrix-vector multiplication
oracle, and a bound `P ⩾ ∥A∥_{1,∞} + 1`, a randomized algorithm computes `Z ∈ R^{n×r}` such that
`ZZ^T ∈ S`, `E F(ZZ^T) ⩽ min_S F + δ`, `r ⩽ O(1 + P⁴ log n/δ⁴)`, where
`F(X) = ⟨A, X⟩ + P · dist_1(diag X, D_K)`. The algorithm uses `O((1 + P/δ)⁵(log n)²)`
matrix-vector multiplications with A and at most n times as many additional operations."

**Formalization Note.**
* Standing assumption of §8 (p.37): `n ⩾ 2`.
* The algorithm is one program `prog` of the real RAM (`Machine`) and the `O(·)` constant is one
  universal `c₀`, both chosen before `n, K, δ, P, A`. Its input is `[n, K, δ, P]`; `A` is reached
  only through the oracle `x ↦ Ax` (`matOracle A`). On every tape it halts after at most
  `c₀(1 + P/δ)⁵(log n)²` oracle calls and at most `n` times as many other steps, with output
  `[r] ++ Z` (row by row) such that `ZZ^T ∈ S` and `r ⩽ c₀(1 + P⁴ log n/δ⁴)`.
* `E F(ZZ^T)` is the integral over the tape measure; its integrability is asserted. `min_S F` is
  `minObj`. -/
theorem theorem_8_2 :
    ∃ c₀ : ℝ, ∃ prog : Program, ∀ n : ℕ, 2 ≤ n → ∀ K δ P : ℝ, 1 ≤ K → 0 < δ → δ ≤ P →
      ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm → norm1inf A + 1 ≤ P →
        (∀ ω : Tape, HaltsWithCounts prog (matOracle A) [(n : ℝ), K, δ, P] ω
          (c₀ * (1 + P / δ) ^ 5 * Real.log n ^ 2) (n * (c₀ * (1 + P / δ) ^ 5 * Real.log n ^ 2))
          (fun out => ∃ (r : ℕ) (Z : Matrix (Fin n) (Fin r) ℝ), FactorCode n r Z out ∧
            Z * Z.transpose ∈ densitySet n ∧ (r : ℝ) ≤ c₀ * (1 + P ^ 4 * Real.log n / δ ^ 4))) ∧
        Integrable (fun ω => objF A P K
          (gramOfList n (finalOut prog (matOracle A) [(n : ℝ), K, δ, P] ω))) tapeMeasure ∧
        ∫ ω, objF A P K (gramOfList n (finalOut prog (matOracle A) [(n : ℝ), K, δ, P] ω))
            ∂tapeMeasure ≤ minObj A P K + δ := by sorry

end OptRobustCD
