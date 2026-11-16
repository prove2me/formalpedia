-- Prove2me | Theorems.Thm_GlobalSinkhorn_Supplement_theorem_4_5
-- name    : GlobalSinkhorn.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:59:25.77127+00:00
-- url     : https://prove2.me/theorems/526062ef-572a-4d1f-aba8-dc68d0e7e84d
-- title:
--   Theorem 4.5 — spectral gap implies weighted buffered expansion: $\sigma<\theta$ gives $A(I,[n]\setminus J)\ge\phi A(I,[n])$
-- statement:
--   Fix $q\in(1/2,1)$ and $\eta>0$, write $\alpha=1+\eta$, and assume $\alpha q<1$ (standing assumptions of §4.2). Let $n\ge2$ and let $A\in\mathbb R^{n\times n}_{\ge0}$ have positive row and column sums; let
--   $$
--   Q_r=\operatorname{diag}\big(A(i,[n])\big)_i,\quad Q_c=\operatorname{diag}\big(A([n],j)\big)_j,\quad B=Q_r^{-1/2}AQ_c^{-1/2},\quad\sigma=s_2(B)
--   $$
--   (Lemma 4.4). Suppose $0<r_-\le r_+<\infty$ and $0<c_-\le c_+<\infty$ satisfy
--   $$
--   r_-\le A(i,[n])\le r_+\ \ \forall i,\qquad c_-\le A([n],j)\le c_+\ \ \forall j,\qquad(84)
--   $$
--   and let
--   $$
--   \theta=\sqrt{\frac{r_-c_-}{r_+c_+}\cdot\frac{1-\alpha q}{\alpha(1-q)}}.\qquad(85)
--   $$
--   If $\sigma<\theta$, then
--   $$
--   \phi=\frac{n\min\{r_-,c_-\}}{A([n],[n])}\,(1-\alpha q)\Big(1-\frac\sigma\theta\Big)>0,\qquad(86)
--   $$
--   and
--
--   1. for every nonempty $I\subseteq[n]$ with $|I|\le qn$ and every $J\subseteq[n]$ with $|J|\le\alpha|I|$: $A(I,[n]\setminus J)\ge\phi\,A(I,[n])$; (87)
--   2. for every nonempty $J\subseteq[n]$ with $|J|\le qn$ and every $I\subseteq[n]$ with $|I|\le\alpha|J|$: $A([n]\setminus I,J)\ge\phi\,A([n],J)$. (88)
--
--   A spectral gap of the margin-normalized matrix, relative to the margin imbalance, forces mass-weighted buffered expansion; $A$ need not be row-stochastic.
--
--   **Formalization Note** $\alpha$ is written $1+\eta$; $\theta$ and $\phi$ are variables pinned by (85) and (86); $\phi>0$ is part of the conclusion.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n}, index sets I, J ⊆ [n] → Fin n (0-based), Finset (Fin n); [n] ∖ J is Jᶜ; |I| compared as a real number; reason: Lean convention; same instances
--   - encoding: s₂(·), second-largest singular value counted with multiplicity → the published GlobalSinkhorn.s2, i.e. (Matrix.toEuclideanLin ·).singularValues 1; reason: Mathlib's singular values are 0-indexed, nonincreasing, with multiplicity; index 1 is the second
--   - encoding: α ≜ 1 + η and the standing assumptions of §4.2 (q ∈ (1/2,1), η > 0, αq < 1) → α written as 1 + η; hypotheses 1/2 < q, q < 1, 0 < η, (1 + η) q < 1; reason: the section's standing assumptions copied into the binders
--   - encoding: B = Q_r^{-1/2} A Q_c^{-1/2}, σ = s₂(B) (Lemma 4.4) → s2 (normalizedMatrix A); reason: the matrix written out; margins positive by hypothesis
--   - encoding: θ ≜ (85), φ ≜ (86) → variables θ, φ with hypotheses θ = (85), φ = (86); reason: a definition by equation; the same values
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 4.5, Eqs. (84)–(88), p.29 (Lemma 4.4, Eqs. (71)–(72), and §4.2 standing assumptions, p.27)

import Mathlib
import Definitions.Def_GlobalSinkhorn_s2
import Definitions.Def_GlobalSinkhorn_Supplement_normalizedMatrix

open Matrix

namespace GlobalSinkhorn.Supplement

/-- Theorem 4.5 (spectral gap implies weighted buffered expansion).
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 4.5, Eqs. (84)–(88), p.29, under the conditions of Lemma 4.4, Eqs. (71)–(72),
and the standing assumptions of §4.2, p.27.

Standing (§4.2): `q ∈ (1/2, 1)`, `η > 0`, `α = 1 + η`, `αq < 1`. Lemma 4.4: `n ≥ 2`, `A ≥ 0`
with positive row and column sums, `B = Q_r^{-1/2} A Q_c^{-1/2}`, `σ = s₂(B)`. If
`0 < r₋ ≤ r₊`, `0 < c₋ ≤ c₊` bound the row and column sums (84),
`θ = √((r₋c₋)/(r₊c₊) · (1 − αq)/(α(1 − q)))` (85) and `σ < θ`, then
`φ = (n min{r₋, c₋} / A([n],[n])) (1 − αq)(1 − σ/θ) > 0` (86), and (87)
`A(I, [n] \ J) ≥ φ A(I, [n])` for nonempty `I`, `|I| ≤ qn`, `|J| ≤ α|I|`; (88)
`A([n] \ I, J) ≥ φ A([n], J)` for nonempty `J`, `|J| ≤ qn`, `|I| ≤ α|J|`.

**Formalization Note.** `α` is written `1 + η`; `θ` and `φ` are variables pinned by the
equations (85) and (86); `φ > 0` is part of the conclusion. `B` is `normalizedMatrix A`.
`A` need not be row-stochastic. `[n] \ J` is `Jᶜ`; set sizes are compared as reals. -/
theorem theorem_4_5 {n : ℕ} (q η : ℝ) (hq₁ : 1 / 2 < q) (hq₂ : q < 1) (hη : 0 < η)
    (hαq : (1 + η) * q < 1) (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, 0 < ∑ j, A i j) (hcol : ∀ j, 0 < ∑ i, A i j)
    (rm rp cm cp : ℝ) (hrm : 0 < rm) (hrmp : rm ≤ rp) (hcm : 0 < cm) (hcmp : cm ≤ cp)
    (hr : ∀ i, rm ≤ ∑ j, A i j ∧ ∑ j, A i j ≤ rp)
    (hc : ∀ j, cm ≤ ∑ i, A i j ∧ ∑ i, A i j ≤ cp)
    (θ : ℝ) (hθ : θ = Real.sqrt (rm * cm / (rp * cp) * ((1 - (1 + η) * q) / ((1 + η) * (1 - q)))))
    (hσ : s2 (normalizedMatrix A) < θ)
    (φ : ℝ) (hφ : φ = n * min rm cm / (∑ i, ∑ j, A i j) * (1 - (1 + η) * q) *
        (1 - s2 (normalizedMatrix A) / θ)) :
    0 < φ ∧
    (∀ I J : Finset (Fin n), I.Nonempty → (I.card : ℝ) ≤ q * n →
      (J.card : ℝ) ≤ (1 + η) * I.card →
      φ * ∑ i ∈ I, ∑ j, A i j ≤ ∑ i ∈ I, ∑ j ∈ Jᶜ, A i j) ∧
    (∀ I J : Finset (Fin n), J.Nonempty → (J.card : ℝ) ≤ q * n →
      (I.card : ℝ) ≤ (1 + η) * J.card →
      φ * ∑ i, ∑ j ∈ J, A i j ≤ ∑ i ∈ Iᶜ, ∑ j ∈ J, A i j) := by sorry

end GlobalSinkhorn.Supplement
