-- Prove2me | Theorems.Thm_OnlineSaddlePoint_Supplement_theorem_4
-- name    : OnlineSaddlePoint.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:57:09.419011+00:00
-- url     : https://prove2.me/theorems/0ed5015a-e65e-4bdb-8324-150ea0d67083
-- title:
--   Theorem 4 (corrected: $\hat A$ zero off the entry $(i',j')$) — the one-point estimate is unbiased, $\mathbb E[\hat A]=A$
-- statement:
--   Let $d_1,d_2\ge2$, $\delta>0$, $x\in\Delta_{X,\delta}$, $y\in\Delta_{Y,\delta}$ (so every coordinate of $x$ and $y$ is at least $\delta$), and let $A$ be a real $d_1\times d_2$ matrix. Sample $i'\sim x$ and $j'\sim y$ independently, and let $\hat A$ be the $d_1\times d_2$ matrix that is zero except in entry $(i',j')$, where $\hat A_{i',j'}=A_{i',j'}/(x_{i'}y_{j'})$. Then
--
--   $$
--   \mathbb E_{i'\sim x,\ j'\sim y}\big[\hat A\big]=\sum_{i'=1}^{d_1}\sum_{j'=1}^{d_2}x_{i'}\,y_{j'}\,\hat A(i',j')=A .
--   $$
--
--   So a single observed entry yields an unbiased estimate of the whole payoff matrix; this is the estimator Bandit-OMG-RFTL feeds to OMG-RFTL under bandit feedback (§5.1).
--
--   Differences from the source:
--   - correction: \"$\hat A_{i,j}=0$ for all $i,j$ such that $i\ne i'$ and $j\ne j'$\" → $\hat A_{i,j}=0$ for all $(i,j)\ne(i',j')$; reason: with the literal condition the entries of row $i'$ and column $j'$ other than $(i',j')$ are unconstrained: for $d_1=d_2=2$, $A=0$, setting $\hat A_{i',j}=1$ for $j\ne j'$ satisfies the printed description but gives $\mathbb E[\hat A]\ne0=A$; the proof on p.20 uses $\hat A=\frac{A_{i',j'}}{x_{i'}y_{j'}}B_{i',j'}$ with $B_{i,j}$ zero except in entry $(i,j)$
--   - encoding: $\mathbb E_{i'\sim x,\,j'\sim y}[\hat A]$ → the finite sum $\sum_{i'}\sum_{j'}x_{i'}y_{j'}\,\hat A(i',j')$; reason: $i'$ and $j'$ are independent (the proof's $\sum_i\sum_j x_iy_j\cdots$), and the expectation of a random variable on a finite space is this sum
--   - encoding: $\mathbb R^{d}$ with $\|\cdot\|_1$ → `PiLp 1 (fun _ : Fin d => ℝ)`, whose norm is $\sum_i|z_i|$; reason: the same normed space
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, Theorem 4, p.19 (proof p.20)

import Mathlib
import Definitions.Def_OnlineSaddlePoint_Supplement_restrictedSimplex
import Definitions.Def_OnlineSaddlePoint_Supplement_onePointEstimate

namespace OnlineSaddlePoint.Supplement

/-- **Theorem 4 (the one-point estimate is unbiased).** Rivera Cardoso, Wang, Xu,
arXiv:1806.08301v3, Theorem 4, p.19: "Let `x ∈ Δ_{X,δ}`, `y ∈ Δ_{Y,δ}` with `d₁, d₂ ≥ 2` and `δ > 0`.
Sample `i′ ∼ x`, `j′ ∼ y`. Let `Â` be the `d₁ × d₂` matrix with `Â_{i,j} = 0` for all `i, j` such that
`i ≠ i′` and `j ≠ j′` and `Â_{i′,j′} = A_{i′,j′}/(x_{i′} y_{j′})`. It holds that
`E_{i′∼x, j′∼y}[Â] = A`."

**Formalization Note.** `i′` and `j′` are drawn independently (the proof on p.20 computes
`E[Â] = ∑_i ∑_j x_i y_j (A_{i,j}/(x_i y_j)) B_{i,j}`), so the expectation of the matrix-valued random
variable is the finite sum `∑_{i′} ∑_{j′} x_{i′} y_{j′} Â(i′, j′)`. `Â(i′, j′)` is
`onePointEstimate A x y i' j'`, zero off the entry `(i′, j′)` (the printed "`i ≠ i′` and `j ≠ j′`"
read as `(i, j) ≠ (i′, j′)`, per the proof). `Δ_{X,δ} = restrictedSimplex d₁ δ` in
`PiLp 1 (fun _ : Fin d₁ => ℝ)`. `A` is any real `d₁ × d₂` matrix. -/
theorem theorem_4 {d₁ d₂ : ℕ} (δ : ℝ) (A : Matrix (Fin d₁) (Fin d₂) ℝ)
    (x : PiLp 1 (fun _ : Fin d₁ => ℝ)) (y : PiLp 1 (fun _ : Fin d₂ => ℝ))
    (hd₁ : 2 ≤ d₁) (hd₂ : 2 ≤ d₂) (hδ : 0 < δ)
    (hx : x ∈ restrictedSimplex d₁ δ) (hy : y ∈ restrictedSimplex d₂ δ) :
    ∑ i', ∑ j', (x i' * y j') • onePointEstimate A x y i' j' = A := by sorry

end OnlineSaddlePoint.Supplement
