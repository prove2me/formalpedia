-- Prove2me | Theorems.Thm_GlobalSinkhorn_theorem_1_1
-- name    : GlobalSinkhorn.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T04:23:39.896571+00:00
-- url     : https://prove2.me/theorems/9b93982b-38b3-4da9-b9aa-6bbb42d06e43
-- title:
--   Theorem 1.1 — Sinkhorn–Knopp reaches marginal $\ell_1$ error $\varepsilon$ within $\lceil (2/g)(8D+\log(16n^3/\varepsilon^2))\rceil$ cycles
-- statement:
--   Let $n\ge2$ and let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic. Suppose $B$ is a doubly stochastic positive diagonal scaling of $A$, and write
--   $$
--   D=D(A;B),\qquad g=1-s_2(B)^2>0,
--   $$
--   where $D(A;B)$ is the optimal logarithmic scaling radius and $s_2(B)$ the second-largest singular value of $B$, counted with multiplicity. Starting from $A^{(0)}=A$, alternately normalize columns and rows, so that $A^{(2t)}$ is the matrix after $t$ complete column–row cycles. Then:
--   1. $A^{(2t)}$ is row-stochastic for every $t$;
--   2. for every $0<\varepsilon\le1$ and every integer $t$ with
--   $$
--   t\ge\Big\lceil\frac{2}{g}\Big(8D+\log\frac{16n^3}{\varepsilon^2}\Big)\Big\rceil ,
--   $$
--   the total marginal error satisfies
--   $$
--   \|r(A^{(2t)})-\mathbf 1\|_1+\|c(A^{(2t)})-\mathbf 1\|_1\le\varepsilon;
--   $$
--   3. (the $O$-bound) for every $0<\varepsilon\le1$, every $t\ge16\,\dfrac{D+\log n+\log(1/\varepsilon)}{g}$ cycles give the same error bound $\varepsilon$.
--
--   The theorem needs no density or expansion assumption on $A$, which may have zero entries; the number of cycles is linear in the scaling radius and inversely proportional to the endpoint spectral gap.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: s₂(S), second-largest singular value counted with multiplicity → (Matrix.toEuclideanLin S).singularValues 1 (0-indexed, with multiplicity); reason: Mathlib's singular values are nonincreasing and 0-indexed; index 1 is the second
--   - encoding: A⁽⁰⁾ = A, then alternately normalize columns and rows; A⁽²ᵗ⁾ after t column–row cycles → skIter A (2 * t), with column step first and Lean's total division; reason: the denominators met are positive under the hypotheses (iterates are M(w_t), p.19), so total division never fires
--   - encoding: standing normalization min_i x_i = min_j y_j of the scaling factors (p.13) → not assumed; reason: replacing (x, y) by (cx, y/c) changes neither the scaled matrix nor any product x_i y_j, so no instance changes
--   - encoding: D(A;B) = min{max(‖u‖∞, ‖v‖∞) : B = diag(e^u) A diag(e^{−v})} → scalingRadius A B, an sInf with Mathlib's sup norm on Fin n → ℝ; reason: the infimum is attained (milestone scalingRadius_attained), so it is the paper's minimum
--   - encoding: "B is a doubly stochastic positive diagonal scaling of A" → B ∈ doublyStochastic ℝ (Fin n) ∧ ∃ x y, IsPosDiagScaling A B x y; reason: the hypothesis written out
--   - encoding: integer t with t ≥ ⌈(2/g)(8D + log(16n³/ε²))⌉ → t : ℕ with (2/g)(8D + log(16n³/ε²)) ≤ (t : ℝ); reason: for an integer t, t ≥ ⌈x⌉ iff x ≤ t; the right side is positive, so t ≥ 1 either way and t : ℕ loses no instance
--   - encoding: ‖r(A⁽²ᵗ⁾) − 1‖₁ + ‖c(A⁽²ᵗ⁾) − 1‖₁ → marginalErr (skIter A (2 * t)); reason: Eq. (14) written out
--   - generalization: "the row-stochastic matrix A⁽²ᵗ⁾" for t satisfying (1) → A⁽²ᵗ⁾ is row-stochastic for every t : ℕ; reason: every even iterate is row-stochastic (t = 0 is the hypothesis on A); the threshold case is a special case
--   - generalization: "the number of required iterations is O((D + log n + log(1/ε))/g)" → every t with 16 (D + log n + log(1/ε))/g ≤ t cycles (2t iterations) gives error ≤ ε; reason: an explicit constant implies the O-claim; 16 suffices because 2(8D + 4 log 2 + 3 log n + 2 log(1/ε)) ≤ 16(D + log n + log(1/ε)) for n ≥ 2, 0 < ε ≤ 1, D ≥ 0 (the paper's last sentence of the proof, p.21)
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 1.1, Eq. (1), p.5

import Mathlib
import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
import Definitions.Def_GlobalSinkhorn_s2
import Definitions.Def_GlobalSinkhorn_scalingRadius
import Definitions.Def_GlobalSinkhorn_skIter
import Definitions.Def_GlobalSinkhorn_marginalErr

open Matrix

namespace GlobalSinkhorn

/-- Theorem 1.1: global convergence of Sinkhorn–Knopp in terms of the scaling radius
`D = D(A; B)` and the gap `g = 1 − s₂(B)²`. He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 1.1, Eq. (1), p.5.

**Formalization Note.** "`B` is a doubly stochastic positive diagonal scaling of `A`" is
`hB` and `hAB`. For an integer `t`, `t ≥ ⌈x⌉` is `x ≤ t`, and the right side of (1) is positive,
so `t : ℕ` loses nothing. The first clause is "the row-stochastic matrix `A⁽²ᵗ⁾`", for every
`t`. The clause "the number of required iterations is `O((D + log n + log(1/ε))/g)`" is stated
with the explicit constant `16`, in cycles (`2t` iterations). No sum met by the iteration is
zero under these hypotheses, so Lean's total division in `skIter` never fires. -/
theorem theorem_1_1 {n : ℕ} (hn : 2 ≤ n) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ (Fin n))
    (hB : B ∈ doublyStochastic ℝ (Fin n))
    (hAB : ∃ x y : Fin n → ℝ, IsPosDiagScaling A B x y)
    (hg : 0 < 1 - s2 B ^ 2) :
    (∀ t : ℕ, skIter A (2 * t) ∈ Matrix.rowStochastic ℝ (Fin n)) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℕ,
      2 / (1 - s2 B ^ 2) *
          (8 * scalingRadius A B + Real.log (16 * (n : ℝ) ^ 3 / ε ^ 2)) ≤ (t : ℝ) →
      marginalErr (skIter A (2 * t)) ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ t : ℕ,
      16 * (scalingRadius A B + Real.log n + Real.log (1 / ε)) / (1 - s2 B ^ 2) ≤ (t : ℝ) →
      marginalErr (skIter A (2 * t)) ≤ ε) := by sorry

end GlobalSinkhorn
