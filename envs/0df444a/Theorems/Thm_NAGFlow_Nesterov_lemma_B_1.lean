-- Prove2me | Theorems.Thm_NAGFlow_Nesterov_lemma_B_1
-- name    : NAGFlow.Nesterov.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:29:53.409714+00:00
-- url     : https://prove2.me/theorems/ac903dca-8d44-4803-99ac-679f4b71fd00
-- title:
--   Lemma B.1, pp. 37–38 — for L_kα_k² = γ_{k+1}, γ_{k+1} = (1 − α_k)γ_k + μα_k: 0 < α_k ≤ 1, α_k ≥ √(min{γ₁, μ}/L), (129) and (130)
-- statement:
--   Let $\gamma_0>0$ and $\mu\ge0$, and let $(L_k)_{k\ge0}$ be a sequence of positive reals with $L_k\ge\mu$. Let $(\alpha_k,\gamma_k)$ satisfy, for every $k$,
--   $$L_k\alpha_k^2=\gamma_{k+1},\qquad \alpha_k>0,\qquad \gamma_{k+1}=(1-\alpha_k)\gamma_k+\mu\alpha_k.\qquad(128)$$
--   Then:
--   1. $\gamma_k>0$ and $0<\alpha_k\le1$ for every $k$;
--   2. $\alpha_k\ge\sqrt{\min\{\gamma_1,\mu\}/L}$ for every $k$, where $L:=\sup_k L_k$;
--   3. for every $k\ge1$,
--   $$\prod_{i=0}^{k-1}(1-\alpha_i)\le\min\left\{4\Big(2+\sum_{i=0}^{k-1}\sqrt{\frac{\gamma_0}{L_i}}\Big)^{-2},\ \Big(1-\sqrt{\frac{\min\{\gamma_1,\mu\}}{L}}\Big)^{k}\right\};\qquad(129)$$
--   4. if $\mu=0$, then for every $k\ge1$,
--   $$\prod_{i=0}^{k-1}(1-\alpha_i)\ge\Big(1+\sum_{i=0}^{k-1}\sqrt{\frac{\gamma_0}{L_i}}\Big)^{-2}.\qquad(130)$$
--
--   The lemma converts the one-step contraction $\mathcal L_{k+1}\le(1-\alpha_k)\mathcal L_k$ into the explicit sublinear and linear rates of Theorem 6.1, uniformly in $\mu\ge0$; for $\mu=0$ and bounded $(L_k)$ the lower bound (130) shows that the product decays exactly at the order $k^{-2}$.
--
--   **Formalization Note.** $L:=\sup_k L_k$ is encoded as "every real upper bound $L$ of $(L_k)$": the bounds involving $L$ get weaker as $L$ grows, so this is equivalent to the page when the supremum is finite, and the part of (129) not involving $L$ is stated for every sequence. The minimum in (129) is split into two inequalities. Negative powers are integer powers of positive reals.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Lemma B.1 and Eqs. (128)–(130), p. 37 (proof pp. 37–38)

import Mathlib

namespace NAGFlow.Nesterov

/-- Lemma B.1 (Luo & Chen, arXiv:1909.03145v4, pp. 37–38). Let `γ₀ > 0`, `μ ≥ 0`, and let `(L_k)` be a
sequence of positive reals with `L_k ≥ μ`. Let `(α_k, γ_k)` satisfy (128):
`L_kα_k² = γ_{k+1}`, `α_k > 0`, `γ_{k+1} = (1 − α_k)γ_k + μα_k` for every `k`. Then

1. `γ_k > 0` for every `k`;
2. `0 < α_k ≤ 1` for every `k`;
3. for every upper bound `L` of `(L_k)` (in particular `L = sup_k L_k`), `α_k ≥ √(min{γ₁, μ}/L)`;
4. for every `k ≥ 1`, `∏_{i<k} (1 − α_i) ≤ 4(2 + Σ_{i<k} √(γ₀/L_i))^{−2}`;
5. for every upper bound `L` of `(L_k)` and every `k ≥ 1`,
   `∏_{i<k} (1 − α_i) ≤ (1 − √(min{γ₁, μ}/L))^k`;
6. (130) if `μ = 0`, then for every `k ≥ 1`, `∏_{i<k} (1 − α_i) ≥ (1 + Σ_{i<k} √(γ₀/L_i))^{−2}`.

Items 4 and 5 together are (129), `∏ ≤ min{…, …}`. -/
theorem lemma_B_1 (μ : ℝ) (α γ Ls : ℕ → ℝ) (hγ0 : 0 < γ 0) (hμ : 0 ≤ μ)
    (hLpos : ∀ k, 0 < Ls k) (hLmu : ∀ k, μ ≤ Ls k)
    (hα : ∀ k, Ls k * α k ^ 2 = γ (k + 1)) (hαpos : ∀ k, 0 < α k)
    (hγ : ∀ k, γ (k + 1) = (1 - α k) * γ k + μ * α k) :
    (∀ k, 0 < γ k) ∧
      (∀ k, 0 < α k ∧ α k ≤ 1) ∧
      (∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k, Real.sqrt (min (γ 1) μ / L) ≤ α k) ∧
      (∀ k : ℕ, 1 ≤ k →
        ∏ i ∈ Finset.range k, (1 - α i) ≤
          4 * (2 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) ^ (-2 : ℤ)) ∧
      (∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k : ℕ, 1 ≤ k →
        ∏ i ∈ Finset.range k, (1 - α i) ≤ (1 - Real.sqrt (min (γ 1) μ / L)) ^ k) ∧
      (μ = 0 → ∀ k : ℕ, 1 ≤ k →
        (1 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) ^ (-2 : ℤ) ≤
          ∏ i ∈ Finset.range k, (1 - α i)) := by sorry

end NAGFlow.Nesterov
