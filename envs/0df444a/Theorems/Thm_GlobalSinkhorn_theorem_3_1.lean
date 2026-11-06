-- Prove2me | Theorems.Thm_GlobalSinkhorn_theorem_3_1
-- name    : GlobalSinkhorn.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T04:23:36.14272+00:00
-- url     : https://prove2.me/theorems/8c2c12e0-a6a2-46ea-abd9-bde123e2936a
-- title:
--   Theorem 3.1 — Sinkhorn–Knopp convergence under product bounds $T^{-1}\le x_iy_j\le T$
-- statement:
--   Let $n\ge2$ and let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic. Suppose $S=XAY$ is doubly stochastic, where $X=\operatorname{diag}(x_1,\dots,x_n)$ and $Y=\operatorname{diag}(y_1,\dots,y_n)$ are positive diagonal matrices. Assume $s_2(S)<1$, $T\ge1$ and $T^{-1}\le x_iy_j\le T$ for all $i,j$. Let $A^{(2t)}$ be the Sinkhorn–Knopp iterate after $t$ full column–row cycles, starting from $A^{(0)}=A$ with a column step. Then:
--   1. for every $0<\varepsilon\le1$ and every integer $t$ with
--   $$
--   t\ge\Big\lceil\frac{2}{1-s_2(S)^4}\Big(4\log T+\log\frac{16n^3}{\varepsilon^2}\Big)\Big\rceil ,
--   $$
--   the matrix $A^{(2t)}$ is row-stochastic and
--   $$
--   \max_{j\in[n]}\Big|\sum_iA^{(2t)}_{ij}-1\Big|\le\frac{\varepsilon}{n};
--   $$
--   2. (the $O$-bound) for every $0<\varepsilon\le1$, every $t\ge 16\,\dfrac{\log n+\log T+\log(1/\varepsilon)}{1-s_2(S)^4}$ full cycles give the same conclusion: $A^{(2t)}$ is row-stochastic and $\max_j|\sum_iA^{(2t)}_{ij}-1|\le\varepsilon/n$.
--
--   Theorem 1.1 follows by choosing $T=e^{2D(A;B)}$.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: s₂(S), second-largest singular value counted with multiplicity → (Matrix.toEuclideanLin S).singularValues 1 (0-indexed, with multiplicity); reason: Mathlib's singular values are nonincreasing and 0-indexed; index 1 is the second
--   - encoding: S nonnegative and doubly stochastic → S ∈ doublyStochastic ℝ (Fin n) (entries ≥ 0, all row and column sums 1); reason: Mathlib's doubly stochastic matrices are exactly the paper's
--   - generalization: standing normalization min_i x_i = min_j y_j of the scaling factors (p.13) → not assumed: any positive x, y with S = XAY; reason: the normalized pair is a special case; (x, y) ↦ (cx, y/c) changes neither S nor any product x_i y_j, and the conclusions mention neither x nor y
--   - encoding: A⁽⁰⁾ = A, then alternately normalize columns and rows; A⁽²ᵗ⁾ after t column–row cycles → skIter A (2 * t), with column step first and Lean's total division; reason: the denominators met are positive under the hypotheses (iterates are M(w_t), p.19), so total division never fires
--   - encoding: integer t with t ≥ ⌈(2/(1 − s₂(S)⁴))(4 log T + log(16n³/ε²))⌉ → t : ℕ with (2/(1 − s₂(S)⁴))(4 log T + log(16n³/ε²)) ≤ (t : ℝ); reason: for an integer t, t ≥ ⌈x⌉ iff x ≤ t; the right side is positive, so t ≥ 1 either way and t : ℕ loses no instance
--   - encoding: max_{j∈[n]} |Σ_i A⁽²ᵗ⁾_ij − 1| ≤ ε/n → ∀ j, |Σ i, skIter A (2t) i j − 1| ≤ ε / n; reason: a bound on the maximum over a finite index set is a bound on every entry
--   - generalization: "the required number of full column–row cycles is O((log n + log T + log(1/ε))/(1 − s₂(S)⁴))" → every t with 16 (log n + log T + log(1/ε))/(1 − s₂(S)⁴) ≤ t gives row-stochasticity and the column bound ε/n; reason: an explicit constant implies the O-claim; 16 suffices because 2(4 log T + 4 log 2 + 3 log n + 2 log(1/ε)) ≤ 16(log n + log T + log(1/ε)) for n ≥ 2, T ≥ 1, 0 < ε ≤ 1
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 3.1, Eqs. (20)–(21), p.15

import Mathlib
import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
import Definitions.Def_GlobalSinkhorn_s2
import Definitions.Def_GlobalSinkhorn_skIter

open Matrix

namespace GlobalSinkhorn

/-- Theorem 3.1: convergence of Sinkhorn–Knopp under product bounds on the scaling.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 3.1, Eqs. (20)–(21), p.15.

**Formalization Note.** For an integer `t`, `t ≥ ⌈x⌉` is `x ≤ t`, and the right side of (20) is
positive, so `t : ℕ` loses nothing. The maximum in (21) is a bound for every `j`. The clause
"`O((log n + log T + log(1/ε))/(1 − s₂(S)⁴))` cycles" is stated with the explicit constant `16`.
The standing normalization `min x = min y` of p.13 is not assumed: it changes neither `S` nor
any product `x i * y j`. Lean's total division in `skIter` never fires under these hypotheses
(every iterate is `M(w)` with positive row and column sums). -/
theorem theorem_3_1 {n : ℕ} (hn : 2 ≤ n) (A S : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ)
    (T : ℝ) (hA : A ∈ Matrix.rowStochastic ℝ (Fin n))
    (hS : S ∈ doublyStochastic ℝ (Fin n))
    (hxy : IsPosDiagScaling A S x y) (hs : s2 S < 1) (hT : 1 ≤ T)
    (hprod : ∀ i j, T⁻¹ ≤ x i * y j ∧ x i * y j ≤ T) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℕ,
      2 / (1 - s2 S ^ 4) * (4 * Real.log T + Real.log (16 * (n : ℝ) ^ 3 / ε ^ 2)) ≤ (t : ℝ) →
      skIter A (2 * t) ∈ Matrix.rowStochastic ℝ (Fin n) ∧
        ∀ j, |∑ i, skIter A (2 * t) i j - 1| ≤ ε / n) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℕ,
      16 * (Real.log n + Real.log T + Real.log (1 / ε)) / (1 - s2 S ^ 4) ≤ (t : ℝ) →
      skIter A (2 * t) ∈ Matrix.rowStochastic ℝ (Fin n) ∧
        ∀ j, |∑ i, skIter A (2 * t) i j - 1| ≤ ε / n) := by sorry

end GlobalSinkhorn
