-- Prove2me | Theorems.Thm_GlobalSinkhorn_Supplement_theorem_1_5
-- name    : GlobalSinkhorn.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:57:00.301895+00:00
-- url     : https://prove2.me/theorems/5e451c0f-dce0-4d6e-9a80-dd2a8bf7ba62
-- title:
--   Theorem 1.5 — mixed spectral certificate: $1-\sqrt K\,\sigma\sigma_\perp>0$ gives distortion $C_0n^\beta$ and $O_{K,\Delta}\big((\log n+\log(1/\varepsilon))/(1-\sigma_\perp^4)\big)$ cycles
-- statement:
--   Let $n\ge2$ and $K\ge1$. Let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic with positive column sums and
--   $$
--   \frac{\max_jA([n],j)}{\min_jA([n],j)}=K.\qquad(7)
--   $$
--   Let $B=XAY$ be doubly stochastic, with positive diagonal $X=\operatorname{diag}(x_1,\dots,x_n)$, $Y=\operatorname{diag}(y_1,\dots,y_n)$. Define
--   $$
--   M=A\,\operatorname{diag}\big(A([n],1),\dots,A([n],n)\big)^{-1/2},\qquad\sigma=s_2(M),\qquad\sigma_\perp=s_2(B),
--   $$
--   and assume $\Delta=1-\sqrt K\,\sigma\,\sigma_\perp>0$. Then there are constants $C_0\ge1$, $\beta>0$, depending only on $K$ and $\Delta$, such that with $T=C_0n^\beta$,
--   $$
--   T^{-1}\le x_iy_j\le T,\qquad T^{-1}A_{ij}\le B_{ij}\le TA_{ij}\qquad\forall i,j\in[n].\qquad(9)
--   $$
--   Moreover, run Sinkhorn–Knopp from $A^{(0)}=A$, alternately normalizing columns and rows. For every $0<\varepsilon\le1$ there is an integer
--   $$
--   t=O_{K,\Delta}\!\left(\frac{\log n+\log(1/\varepsilon)}{1-\sigma_\perp^4}\right)
--   $$
--   such that $\|r(A^{(2t)})-\mathbf 1\|_1+\|c(A^{(2t)})-\mathbf 1\|_1\le\varepsilon$, where $r,c$ are the row and column sums and $A^{(2t)}$ is the matrix after $t$ full column–row cycles. (10)
--
--   The hypothesis uses the spectrum of the endpoint $B$ and is weaker than the input-only criterion of Theorem 1.4.
--
--   **Formalization Note** One set of constants $C_0,\beta,C$ is chosen after $K$ and $\Delta$ and before everything else; the $O$-bound is $t\le C(\log n+\log(1/\varepsilon))/(1-\sigma_\perp^4)$. The paper proves $\sigma_\perp<1$ from the hypotheses, so the denominator is positive; it is not assumed.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n}, index sets I, J ⊆ [n] → Fin n (0-based), Finset (Fin n); [n] ∖ J is Jᶜ; |I| compared as a real number; reason: Lean convention; same instances
--   - encoding: s₂(·), second-largest singular value counted with multiplicity → the published GlobalSinkhorn.s2, i.e. (Matrix.toEuclideanLin ·).singularValues 1; reason: Mathlib's singular values are 0-indexed, nonincreasing, with multiplicity; index 1 is the second
--   - encoding: A ∈ ℝ^{n×n}_{≥0} row-stochastic → A ∈ Matrix.rowStochastic ℝ (Fin n); reason: Mathlib's definition includes nonnegativity
--   - encoding: max_j A([n],j) / min_j A([n],j) = K → (⨆ j, ∑ i, A i j) / (⨅ j, ∑ i, A i j) = K; reason: over the finite nonempty Fin n (n ≥ 2) the real iSup/iInf are the maximum and minimum
--   - encoding: M = A diag(A([n],1),…,A([n],n))^{-1/2} → A * diagonal (fun j => (√(∑ i, A i j))⁻¹); reason: the matrix written out; column sums are positive by hypothesis, so the total square root and inverse never meet 0
--   - encoding: B doubly stochastic → B ∈ Matrix.doublyStochastic ℝ (Fin n); reason: Mathlib's definition: nonnegative entries, row and column sums 1
--   - encoding: B = XAY with X = diag(x), Y = diag(y) positive diagonal → the published GlobalSinkhorn.IsPosDiagScaling A B x y; reason: the same predicate (x, y > 0 and B = diag x · A · diag y)
--   - encoding: standing normalization min_i x_i = min_j y_j of the scaling factors (p.13) → not imposed; reason: replacing (x, y) by (tx, y/t) changes neither B nor any product x_i y_j, the only quantities in the statement, so no instance changes
--   - encoding: constants C₀ ≥ 1, β > 0 and the O_{K,Δ}-constant depending only on K and Δ → ∀ K ≥ 1, ∀ Δ > 0, ∃ C₀ ≥ 1, β > 0, C > 0, ∀ n ≥ 2, ∀ A B x y with 1 − √K σ σ⊥ = Δ; reason: the dependence written as quantifier order
--   - encoding: some integer t = O_{K,Δ}((log n + log(1/ε))/(1 − σ⊥⁴)) → ∃ t : ℕ, (t : ℝ) ≤ C (log n + log(1/ε)) / (1 − σ⊥⁴); reason: t counts cycles and is nonnegative; for n ≥ 2 and ε ≤ 1 the bracket is at least log 2 > 0, so a multiplicative constant expresses the O-bound
--   - encoding: SK iterates A⁽²ᵗ⁾ (t column–row cycles) and the error ‖r(·)−1‖₁ + ‖c(·)−1‖₁ of (14) → marginalErr (skIter A (2 * t)) with the published skIter (one normalization per index, column step first) and marginalErr; reason: the published definitions of the base mission; the denominators met are positive, so total division never fires
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 1.5, Eqs. (7)–(10), pp.7–8

import Mathlib
import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
import Definitions.Def_GlobalSinkhorn_s2
import Definitions.Def_GlobalSinkhorn_skIter
import Definitions.Def_GlobalSinkhorn_marginalErr

open Matrix

namespace GlobalSinkhorn.Supplement

/-- Theorem 1.5 (mixed spectral certificate and Sinkhorn–Knopp bound).
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 1.5, Eqs. (7)–(10), pp.7–8.

Let `n ≥ 2`, `K ≥ 1`, let `A` be nonnegative and row-stochastic with positive column sums and
column-sum ratio exactly `K`, and let `B = XAY` be doubly stochastic with positive diagonal
`X = diag x`, `Y = diag y`. With `σ = s₂(A diag(c)^{-1/2})`, `σ⊥ = s₂(B)` and
`Δ = 1 − √K σ σ⊥ > 0`: (9) `T⁻¹ ≤ xᵢ yⱼ ≤ T`, `T⁻¹ Aᵢⱼ ≤ Bᵢⱼ ≤ T Aᵢⱼ` with `T = C₀ n^β`; and
(10) for every `0 < ε ≤ 1` some integer `t = O_{K,Δ}((log n + log(1/ε))/(1 − σ⊥⁴))` has
`‖r(A⁽²ᵗ⁾) − 1‖₁ + ‖c(A⁽²ᵗ⁾) − 1‖₁ ≤ ε`.

**Formalization Note.** The constants `C₀ ≥ 1`, `β > 0` and the `O`-constant `C > 0` depend
only on `K` and `Δ`: `∀ K Δ, ∃ C₀ β C, ∀ n A B x y`, with the hypothesis
`1 − √K σ σ⊥ = Δ`. The bounds (9) are for the given `x, y`. `A⁽²ᵗ⁾` is
`skIter A (2 * t)` (`t` column–row cycles). `σ⊥ < 1` is not assumed: the paper derives it
from the hypotheses (proof of Theorem 1.5, p.34), so the division by `1 − σ⊥⁴` is never by
zero. The column-sum ratio is `(⨆ j, cⱼ) / (⨅ j, cⱼ)` over the nonempty finite `Fin n`. -/
theorem theorem_1_5 :
    ∀ K : ℝ, 1 ≤ K → ∀ Δ : ℝ, 0 < Δ →
    ∃ C₀ β C : ℝ, 1 ≤ C₀ ∧ 0 < β ∧ 0 < C ∧
    ∀ n : ℕ, 2 ≤ n → ∀ (A B : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ),
      A ∈ Matrix.rowStochastic ℝ (Fin n) →
      (∀ j, 0 < ∑ i, A i j) →
      (⨆ j, ∑ i, A i j) / (⨅ j, ∑ i, A i j) = K →
      B ∈ doublyStochastic ℝ (Fin n) →
      IsPosDiagScaling A B x y →
      1 - Real.sqrt K *
          s2 (A * Matrix.diagonal (fun j => (Real.sqrt (∑ i, A i j))⁻¹)) * s2 B = Δ →
      (∀ i j,
          (C₀ * (n : ℝ) ^ β)⁻¹ ≤ x i * y j ∧ x i * y j ≤ C₀ * (n : ℝ) ^ β ∧
          (C₀ * (n : ℝ) ^ β)⁻¹ * A i j ≤ B i j ∧ B i j ≤ C₀ * (n : ℝ) ^ β * A i j) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ t : ℕ, (t : ℝ) ≤ C * (Real.log n + Real.log (1 / ε)) / (1 - s2 B ^ 4) ∧
          marginalErr (skIter A (2 * t)) ≤ ε) := by sorry

end GlobalSinkhorn.Supplement
