-- Prove2me | Theorems.Thm_GlobalSinkhorn_Supplement_theorem_4_6
-- name    : GlobalSinkhorn.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:00:01.247267+00:00
-- url     : https://prove2.me/theorems/278725f2-e67b-4837-8f17-f5e763bfde34
-- title:
--   Theorem 4.6 — row-stochastic spectral criterion $\sigma\le(1-\delta)\theta_K$ implies $(q,\eta,\zeta)$-buffered robust vertex expansion
-- statement:
--   Fix $q\in(1/2,1)$ and $\eta>0$, write $\alpha=1+\eta$, and assume $\alpha q<1$ (§4.2). Let $n\ge2$ and $K\ge1$, and let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic with positive column sums. Let
--   $$
--   Q=\operatorname{diag}\big(A([n],1),\dots,A([n],n)\big),\qquad\sigma=s_2(AQ^{-1/2}),
--   $$
--   and suppose
--   $$
--   \frac{\max_jA([n],j)}{\min_jA([n],j)}\le K.\qquad(97)
--   $$
--   Let $\theta_K=\sqrt{\dfrac{1-\alpha q}{K\alpha(1-q)}}$ (98), let $\delta\in(0,1)$, and assume $\sigma\le(1-\delta)\theta_K$. With
--   $$
--   \zeta=\frac{\delta(1-\alpha q)}{K-(K-1)(1-\alpha q)}\qquad(99)
--   $$
--   the following hold:
--
--   1. for every nonempty $I$ with $|I|\le qn$ and every $J$ with $|J|\le\alpha|I|$: $A(I,[n]\setminus J)\ge\zeta|I|$; (100)
--   2. for every nonempty $J$ with $|J|\le qn$ and every $I$ with $|I|\le\alpha|J|$: $A([n]\setminus I,J)\ge\zeta|J|$; (101)
--   3. consequently $A$ satisfies $(q,\eta,\zeta)$-two-sided buffered robust vertex expansion (Definition 2.3).
--
--   This is the input-only spectral route to the expansion hypothesis of Theorem 4.1.
--
--   **Formalization Note** $\alpha$ is written $1+\eta$; $\theta_K$ and $\zeta$ are written out. All three conclusions are kept; the third uses the predicate of Definition 2.3, which also records $\zeta>0$ and the definition's context.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n}, index sets I, J ⊆ [n] → Fin n (0-based), Finset (Fin n); [n] ∖ J is Jᶜ; |I| compared as a real number; reason: Lean convention; same instances
--   - encoding: s₂(·), second-largest singular value counted with multiplicity → the published GlobalSinkhorn.s2, i.e. (Matrix.toEuclideanLin ·).singularValues 1; reason: Mathlib's singular values are 0-indexed, nonincreasing, with multiplicity; index 1 is the second
--   - encoding: A ∈ ℝ^{n×n}_{≥0} row-stochastic → A ∈ Matrix.rowStochastic ℝ (Fin n); reason: Mathlib's definition includes nonnegativity
--   - encoding: α ≜ 1 + η and the standing assumptions of §4.2 (q ∈ (1/2,1), η > 0, αq < 1) → α written as 1 + η; hypotheses 1/2 < q, q < 1, 0 < η, (1 + η) q < 1; reason: the section's standing assumptions copied into the binders
--   - encoding: max_j A([n],j) / min_j A([n],j) ≤ K → (⨆ j, ∑ i, A i j) / (⨅ j, ∑ i, A i j) ≤ K; reason: over the finite nonempty Fin n (n ≥ 2) the real iSup/iInf are the maximum and minimum
--   - encoding: σ = s₂(A Q^{-1/2}) → s2 (A * diagonal (fun j => (√(∑ i, A i j))⁻¹)); reason: the matrix written out; column sums positive by hypothesis
--   - encoding: θ_K ≜ (98), ζ ≜ (99) → the expressions substituted in place; reason: a definition by equation; the same values
--   - encoding: A satisfies (q, η, ζ)-two-sided buffered robust vertex expansion → IsBufferedExpansion q η ζ A, whose first conjuncts are the context of Definition 2.3 (n ≥ 2, q ∈ (1/2,1), η > 0, ζ > 0, q(1+η) < 1, A row-stochastic); reason: the definition's context holds under the theorem's hypotheses (ζ > 0 since δ > 0 and αq < 1)
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 4.6, Eqs. (97)–(101), p.30 (§4.2 standing assumptions, p.27)

import Mathlib
import Definitions.Def_GlobalSinkhorn_s2
import Definitions.Def_GlobalSinkhorn_Supplement_IsBufferedExpansion

open Matrix

namespace GlobalSinkhorn.Supplement

/-- Theorem 4.6 (row-stochastic spectral criterion for buffered robust vertex expansion).
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 4.6, Eqs. (97)–(101), p.30, under the standing assumptions of §4.2, p.27.

Standing (§4.2): `q ∈ (1/2, 1)`, `η > 0`, `α = 1 + η`, `αq < 1`. Let `n ≥ 2`, `K ≥ 1`, `A ≥ 0`
row-stochastic with positive column sums, `Q = diag(A([n],1), …, A([n],n))`,
`σ = s₂(A Q^{-1/2})`, column-sum ratio at most `K` (97), `θ_K = √((1 − αq)/(Kα(1 − q)))`
(98), `δ ∈ (0, 1)` and `σ ≤ (1 − δ)θ_K`. With `ζ = δ(1 − αq)/(K − (K − 1)(1 − αq))` (99):
(100) `A(I, [n] \ J) ≥ ζ|I|` for nonempty `I`, `|I| ≤ qn`, `|J| ≤ α|I|`; (101)
`A([n] \ I, J) ≥ ζ|J|` for nonempty `J`, `|J| ≤ qn`, `|I| ≤ α|J|`; consequently `A`
satisfies `(q, η, ζ)`-two-sided buffered robust vertex expansion (Definition 2.3).

**Formalization Note.** `α` is written `1 + η`. The ratio in (97) is
`(⨆ j, cⱼ) / (⨅ j, cⱼ)` over the nonempty finite `Fin n`. `θ_K` and `ζ` are written out.
All three conclusions are kept; the last is the predicate of Definition 2.3,
`IsBufferedExpansion q η ζ A`, which also records `ζ > 0` and the standing data. -/
theorem theorem_4_6 {n : ℕ} (q η : ℝ) (hq₁ : 1 / 2 < q) (hq₂ : q < 1) (hη : 0 < η)
    (hαq : (1 + η) * q < 1) (hn : 2 ≤ n) (K : ℝ) (hK : 1 ≤ K)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.rowStochastic ℝ (Fin n))
    (hcol : ∀ j, 0 < ∑ i, A i j)
    (hratio : (⨆ j, ∑ i, A i j) / (⨅ j, ∑ i, A i j) ≤ K)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hσ : s2 (A * Matrix.diagonal (fun j => (Real.sqrt (∑ i, A i j))⁻¹)) ≤
      (1 - δ) * Real.sqrt ((1 - (1 + η) * q) / (K * (1 + η) * (1 - q)))) :
    (∀ I J : Finset (Fin n), I.Nonempty → (I.card : ℝ) ≤ q * n →
      (J.card : ℝ) ≤ (1 + η) * I.card →
      δ * (1 - (1 + η) * q) / (K - (K - 1) * (1 - (1 + η) * q)) * I.card ≤
        ∑ i ∈ I, ∑ j ∈ Jᶜ, A i j) ∧
    (∀ I J : Finset (Fin n), J.Nonempty → (J.card : ℝ) ≤ q * n →
      (I.card : ℝ) ≤ (1 + η) * J.card →
      δ * (1 - (1 + η) * q) / (K - (K - 1) * (1 - (1 + η) * q)) * J.card ≤
        ∑ i ∈ Iᶜ, ∑ j ∈ J, A i j) ∧
    IsBufferedExpansion q η (δ * (1 - (1 + η) * q) / (K - (K - 1) * (1 - (1 + η) * q))) A := by sorry

end GlobalSinkhorn.Supplement
