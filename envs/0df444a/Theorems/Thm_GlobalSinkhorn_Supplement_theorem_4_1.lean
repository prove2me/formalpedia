-- Prove2me | Theorems.Thm_GlobalSinkhorn_Supplement_theorem_4_1
-- name    : GlobalSinkhorn.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:58:57.019392+00:00
-- url     : https://prove2.me/theorems/f5f8bca8-17c5-41c0-b350-ab20d9108247
-- title:
--   Theorem 4.1 — structural stability from buffered expansion: $T^{-1}\le x_iy_j\le T$ with $T\le\frac{Cn}{(1+c)(1+\eta)\lfloor qn\rfloor-n}(qn/m)^\beta$
-- statement:
--   Let $n\ge2$, $\kappa>0$, $q\in(1/2,1)$, $\eta,\phi\in(0,1)$ and $0<c\le1$, with
--   $$
--   q(1+\eta)<1,\qquad c(1+\eta)>1,\qquad(1+c)(1+\eta)\lfloor qn\rfloor>n.\qquad(38)
--   $$
--   Let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic and $B=XAY$ with positive diagonal $X=\operatorname{diag}(x_i)$, $Y=\operatorname{diag}(y_j)$, $\min_ix_i=\min_jy_j=\kappa$. Suppose that for some $0<s_-\le1\le s_+<\infty$ and $b_+\ge1$,
--   $$
--   s_-\le A([n],j)\le s_+,\qquad B([n],j)=1,\qquad B(j,[n])\le b_+\qquad\forall j.\qquad(39)\text{–}(40)
--   $$
--   Let $1\le m\le\lfloor qn\rfloor$ be an integer such that:
--
--   1. $c|I|\le B(I,[n])\le c^{-1}|I|$ for every $I$ with $|I|\ge m$; (41)
--   2. $A(I,[n]\setminus J)\ge\phi|I|$ whenever $m\le|I|\le qn$ and $|J|\le(1+\eta)|I|$, and $A([n]\setminus I,J)\ge\phi|J|$ whenever $m\le|J|\le qn$ and $|I|\le(1+\eta)|J|$; (42)–(43)
--   3. there are sets $R_0,C_0$ with $|R_0|,|C_0|\ge m$ and constants $H_x,H_y>0$ with $x_i\ge H_x/\kappa$ on $R_0$ and $y_j\ge H_y/\kappa$ on $C_0$. (44)
--
--   Then there are constants $C\ge1$, $\beta>0$, depending only on $c,\eta,\phi,s_-,s_+,b_+,H_x,H_y$, and a number $T\ge1$ with
--   $$
--   T\le\frac{Cn}{(1+c)(1+\eta)\lfloor qn\rfloor-n}\Big(\frac{qn}{m}\Big)^{\beta},\qquad(45)
--   $$
--   $$
--   \frac1T\le x_iy_j\le T,\qquad\frac{A_{ij}}T\le B_{ij}\le TA_{ij}\qquad\forall i,j.\qquad(46)
--   $$
--
--   Here $A(I,J)=\sum_{i\in I,j\in J}A_{ij}$. With seeds of linear size ($m=\Theta(n)$) the distortion $T$ is a constant, and in general it is polynomial in $n$.
--
--   **Formalization Note** The eight parameters $c,\eta,\phi,s_-,s_+,b_+,H_x,H_y$ and their own conditions (including $c(1+\eta)>1$ from (38)) are quantified before $\exists C,\beta$; $n,\kappa,q,A,B,x,y,m,R_0,C_0$ after; $T$ is existential per instance. $\lfloor qn\rfloor$ is `Nat.floor`, and $\min_ix_i=\kappa$ is "$\kappa\le x_i$ for all $i$, with equality for some $i$".
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n}, index sets I, J ⊆ [n] → Fin n (0-based), Finset (Fin n); [n] ∖ J is Jᶜ; |I| compared as a real number; reason: Lean convention; same instances
--   - encoding: A ∈ ℝ^{n×n}_{≥0} row-stochastic → A ∈ Matrix.rowStochastic ℝ (Fin n); reason: Mathlib's definition includes nonnegativity
--   - encoding: B = XAY with X = diag(x), Y = diag(y) positive diagonal → the published GlobalSinkhorn.IsPosDiagScaling A B x y; reason: the same predicate (x, y > 0 and B = diag x · A · diag y)
--   - encoding: constants C ≥ 1, β > 0 depending only on c, η, φ, s₋, s₊, b₊, H_x, H_y, and a number T ≥ 1 → ∀ c η φ s₋ s₊ b₊ H_x H_y (with their range conditions, including c(1 + η) > 1), ∃ C ≥ 1, ∃ β > 0, ∀ n κ q A B x y m R₀ C₀ (hypotheses), ∃ T ≥ 1; reason: the dependence written as quantifier order; a condition on the eight parameters alone may be stated before ∃ C β without changing any instance
--   - encoding: min_i x_i = min_j y_j = κ → (∀ i, κ ≤ x i) ∧ (∃ i, x i = κ), and the same for y; reason: the minimum over the nonempty finite Fin n written out
--   - encoding: ⌊qn⌋ and (qn/m)^β → Nat.floor (q * n) and the real power; reason: Lean convention; q n ≥ 0 so the floor is the integer part
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 4.1, Eqs. (38)–(46), p.22

import Mathlib
import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling

open Matrix

namespace GlobalSinkhorn.Supplement

/-- Theorem 4.1 (structural stability from buffered expansion).
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 4.1, Eqs. (38)–(46), p.22.

Hypotheses: `n ≥ 2`, `κ > 0`, `q ∈ (1/2, 1)`, `η, φ ∈ (0, 1)`, `0 < c ≤ 1`; (38)
`q(1 + η) < 1`, `c(1 + η) > 1`, `(1 + c)(1 + η)⌊qn⌋ > n`; `A` nonnegative row-stochastic;
`B = XAY` with positive diagonal `X = diag x`, `Y = diag y`, `min x = min y = κ`;
`0 < s₋ ≤ 1 ≤ s₊`, `b₊ ≥ 1`; (39) `s₋ ≤ A([n], j) ≤ s₊`; (40) `B([n], j) = 1`, `B(j, [n]) ≤ b₊`;
an integer `1 ≤ m ≤ ⌊qn⌋`; (41) `c|I| ≤ B(I, [n]) ≤ c⁻¹|I|` for `|I| ≥ m`; (42)–(43) buffered
expansion with constant `φ` on the scales `m ≤ |I| ≤ qn` (resp. `|J|`); (44) seeds
`R₀, C₀` with `|R₀|, |C₀| ≥ m`, `xᵢ ≥ H_x/κ` on `R₀`, `yⱼ ≥ H_y/κ` on `C₀`, `H_x, H_y > 0`.
Conclusion: constants `C ≥ 1`, `β > 0` depending only on `c, η, φ, s₋, s₊, b₊, H_x, H_y`, and a
number `T ≥ 1` with (45) `T ≤ (C n / ((1 + c)(1 + η)⌊qn⌋ − n)) (qn/m)^β` and (46)
`1/T ≤ xᵢ yⱼ ≤ T`, `Aᵢⱼ/T ≤ Bᵢⱼ ≤ T Aᵢⱼ`.

**Formalization Note.** The eight listed parameters and their own range conditions
(including `c(1 + η) > 1` from (38)) are quantified before `∃ C β`; everything else (`n, κ,
q, A, B, x, y, m, R₀, C₀`) after, and `T` is existential per instance. `⌊qn⌋` is
`Nat.floor (q * n)`; `min_i xᵢ = κ` is `(∀ i, κ ≤ xᵢ) ∧ ∃ i, xᵢ = κ`; `[n] \ J` is `Jᶜ`;
`A(I, J) = ∑_{i∈I} ∑_{j∈J} A i j`; set sizes are compared as reals; `(qn/m)^β` is the real
power. The denominator in (45) is positive by (38). -/
theorem theorem_4_1 :
    ∀ c η φ sm sp bp Hx Hy : ℝ,
      0 < c → c ≤ 1 → 0 < η → η < 1 → 0 < φ → φ < 1 → 1 < c * (1 + η) →
      0 < sm → sm ≤ 1 → 1 ≤ sp → 1 ≤ bp → 0 < Hx → 0 < Hy →
    ∃ C β : ℝ, 1 ≤ C ∧ 0 < β ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ κ q : ℝ, 0 < κ → 1 / 2 < q → q < 1 →
      q * (1 + η) < 1 →
      (n : ℝ) < (1 + c) * (1 + η) * (⌊q * n⌋₊ : ℝ) →
      ∀ (A B : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ),
      A ∈ Matrix.rowStochastic ℝ (Fin n) →
      IsPosDiagScaling A B x y →
      (∀ i, κ ≤ x i) → (∃ i, x i = κ) →
      (∀ j, κ ≤ y j) → (∃ j, y j = κ) →
      (∀ j, sm ≤ ∑ i, A i j ∧ ∑ i, A i j ≤ sp) →
      (∀ j, ∑ i, B i j = 1 ∧ ∑ k, B j k ≤ bp) →
      ∀ m : ℕ, 1 ≤ m → m ≤ ⌊q * n⌋₊ →
      (∀ I : Finset (Fin n), m ≤ I.card →
          c * I.card ≤ ∑ i ∈ I, ∑ j, B i j ∧ ∑ i ∈ I, ∑ j, B i j ≤ c⁻¹ * I.card) →
      (∀ I J : Finset (Fin n), m ≤ I.card → (I.card : ℝ) ≤ q * n →
          (J.card : ℝ) ≤ (1 + η) * I.card →
          φ * I.card ≤ ∑ i ∈ I, ∑ j ∈ Jᶜ, A i j) →
      (∀ I J : Finset (Fin n), m ≤ J.card → (J.card : ℝ) ≤ q * n →
          (I.card : ℝ) ≤ (1 + η) * J.card →
          φ * J.card ≤ ∑ i ∈ Iᶜ, ∑ j ∈ J, A i j) →
      ∀ R₀ C₀ : Finset (Fin n), m ≤ R₀.card → m ≤ C₀.card →
      (∀ i ∈ R₀, Hx / κ ≤ x i) → (∀ j ∈ C₀, Hy / κ ≤ y j) →
      ∃ T : ℝ, 1 ≤ T ∧
        T ≤ C * n / ((1 + c) * (1 + η) * (⌊q * n⌋₊ : ℝ) - n) *
          (q * n / m) ^ β ∧
        ∀ i j, 1 / T ≤ x i * y j ∧ x i * y j ≤ T ∧
          A i j / T ≤ B i j ∧ B i j ≤ T * A i j := by sorry

end GlobalSinkhorn.Supplement
