-- Prove2me | Theorems.Thm_GlobalSinkhorn_Supplement_theorem_1_4
-- name    : GlobalSinkhorn.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:56:35.753593+00:00
-- url     : https://prove2.me/theorems/ebc7dddb-81ce-4f38-be49-a95707b3a0a7
-- title:
--   Theorem 1.4 — input-only spectral certificate: $1-\sqrt K\,\sigma>0$ gives a doubly stochastic scaling with distortion $T=C_0n^\beta$
-- statement:
--   Let $n\ge2$ and $K\ge1$. Let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic with positive column sums $A([n],j)=\sum_iA_{ij}$, and suppose
--   $$
--   \frac{\max_jA([n],j)}{\min_jA([n],j)}=K.\qquad(6)
--   $$
--   Let $M=A\,\operatorname{diag}\big(A([n],1),\dots,A([n],n)\big)^{-1/2}$ and $\sigma=s_2(M)$, its second-largest singular value. If $1-\sqrt K\,\sigma>0$, then there is a doubly stochastic matrix $B=XAY$ with positive diagonal $X=\operatorname{diag}(x_1,\dots,x_n)$, $Y=\operatorname{diag}(y_1,\dots,y_n)$. Moreover there are constants $C_0\ge1$ and $\beta>0$, depending only on $K$ and $1-\sqrt K\sigma$, such that with $T=C_0n^\beta$,
--   $$
--   T^{-1}\le x_iy_j\le T,\qquad T^{-1}A_{ij}\le B_{ij}\le TA_{ij}\qquad\forall i,j\in[n].
--   $$
--
--   Both quantities in the hypothesis are computed from $A$ alone. The product bounds give a scaling radius $D(A;B)\le\log C_0+\beta\log n$, which Theorem 1.1 turns into an iteration bound.
--
--   **Formalization Note** "Depending only on $K$ and $1-\sqrt K\sigma$" is the quantifier order $\forall K\ \forall\delta>0\ \exists C_0,\beta\ \forall n,A$ with the hypothesis $1-\sqrt K\sigma=\delta$; $n^\beta$ is the real power.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n}, index sets I, J ⊆ [n] → Fin n (0-based), Finset (Fin n); [n] ∖ J is Jᶜ; |I| compared as a real number; reason: Lean convention; same instances
--   - encoding: s₂(·), second-largest singular value counted with multiplicity → the published GlobalSinkhorn.s2, i.e. (Matrix.toEuclideanLin ·).singularValues 1; reason: Mathlib's singular values are 0-indexed, nonincreasing, with multiplicity; index 1 is the second
--   - encoding: A ∈ ℝ^{n×n}_{≥0} row-stochastic → A ∈ Matrix.rowStochastic ℝ (Fin n); reason: Mathlib's definition includes nonnegativity
--   - encoding: max_j A([n],j) / min_j A([n],j) = K → (⨆ j, ∑ i, A i j) / (⨅ j, ∑ i, A i j) = K; reason: over the finite nonempty Fin n (n ≥ 2) the real iSup/iInf are the maximum and minimum
--   - encoding: M = A diag(A([n],1),…,A([n],n))^{-1/2} → A * diagonal (fun j => (√(∑ i, A i j))⁻¹); reason: the matrix written out; column sums are positive by hypothesis, so the total square root and inverse never meet 0
--   - encoding: constants C₀ ≥ 1, β > 0 depending only on K and 1 − √K σ → ∀ K ≥ 1, ∀ δ > 0, ∃ C₀ ≥ 1, ∃ β > 0, ∀ n ≥ 2, ∀ A with 1 − √K σ = δ; reason: the dependence written as quantifier order; δ ranges over the positive values of 1 − √K σ
--   - encoding: there exists a doubly-stochastic B = XAY with X, Y positive diagonal, and the bounds hold for its x_i, y_j → ∃ B x y, B ∈ doublyStochastic ℝ (Fin n) ∧ IsPosDiagScaling A B x y ∧ the bounds; reason: the existential written out with the published scaling predicate
--   - encoding: standing normalization min_i x_i = min_j y_j of the scaling factors (p.13) → not imposed; reason: replacing (x, y) by (tx, y/t) changes neither B nor any product x_i y_j, the only quantities in the statement, so no instance changes
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 1.4, Eq. (6), p.7

import Mathlib
import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
import Definitions.Def_GlobalSinkhorn_s2

open Matrix

namespace GlobalSinkhorn.Supplement

/-- Theorem 1.4 (input-only certificate for a polynomial scaling distortion).
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 1.4, Eq. (6), p.7.

Let `n ≥ 2`, `K ≥ 1`, let `A` be nonnegative and row-stochastic with positive column sums
whose ratio of largest to smallest column sum is exactly `K`, and let
`σ = s₂(A diag(A([n],1), …, A([n],n))^{-1/2})`. If `δ = 1 − √K σ > 0`, then a doubly
stochastic `B = XAY` with positive diagonal `X = diag x`, `Y = diag y` exists, and with
`T = C₀ n^β`, `T⁻¹ ≤ xᵢ yⱼ ≤ T` and `T⁻¹ Aᵢⱼ ≤ Bᵢⱼ ≤ T Aᵢⱼ` for all `i, j`.

**Formalization Note.** "Constants `C₀ ≥ 1`, `β > 0` depending only on `K` and `1 − √Kσ`" is
`∀ K δ, ∃ C₀ β, ∀ n A`, with the hypothesis `1 − √K σ = δ`; `n^β` is the real power. The
column-sum ratio `max_j / min_j` is `(⨆ j, cⱼ) / (⨅ j, cⱼ)` over the finite nonempty `Fin n`
(`n ≥ 2`), where real `iSup`/`iInf` are the maximum and minimum. `(√cⱼ)⁻¹` is total but
`cⱼ > 0` by hypothesis. Indices are `Fin n`; `s₂` is the published `GlobalSinkhorn.s2`. -/
theorem theorem_1_4 :
    ∀ K : ℝ, 1 ≤ K → ∀ δ : ℝ, 0 < δ →
    ∃ C₀ β : ℝ, 1 ≤ C₀ ∧ 0 < β ∧
    ∀ n : ℕ, 2 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
      A ∈ Matrix.rowStochastic ℝ (Fin n) →
      (∀ j, 0 < ∑ i, A i j) →
      (⨆ j, ∑ i, A i j) / (⨅ j, ∑ i, A i j) = K →
      1 - Real.sqrt K *
          s2 (A * Matrix.diagonal (fun j => (Real.sqrt (∑ i, A i j))⁻¹)) = δ →
      ∃ (B : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ),
        B ∈ doublyStochastic ℝ (Fin n) ∧ IsPosDiagScaling A B x y ∧
        ∀ i j,
          (C₀ * (n : ℝ) ^ β)⁻¹ ≤ x i * y j ∧ x i * y j ≤ C₀ * (n : ℝ) ^ β ∧
          (C₀ * (n : ℝ) ^ β)⁻¹ * A i j ≤ B i j ∧ B i j ≤ C₀ * (n : ℝ) ^ β * A i j := by sorry

end GlobalSinkhorn.Supplement
