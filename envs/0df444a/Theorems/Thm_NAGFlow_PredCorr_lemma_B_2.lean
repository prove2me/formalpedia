-- Prove2me | Theorems.Thm_NAGFlow_PredCorr_lemma_B_2
-- name    : NAGFlow.PredCorr.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:29:56.920526+00:00
-- url     : https://prove2.me/theorems/53cdc5a3-5a4b-42d5-aab6-f97af358a8c9
-- title:
--   Lemma B.2, pp. 38–39 — γ_k > 0, α_k ≥ √(min{γ₀, μ}/L), and two-sided bounds on ∏_{i<k} 1/(1 + α_i)
-- statement:
--   Let $\gamma_0>0$ and $\mu\ge0$, and let $(L_k)$ be a sequence of positive reals with $L_k\ge\mu$ for all $k$. Let $(\alpha_k,\gamma_k)$ satisfy, for every $k$,
--   $$\gamma_{k+1}=\gamma_k+\alpha_k(\mu-\gamma_{k+1}),\qquad L_k\alpha_k^2=\gamma_k(1+\alpha_k),\qquad \alpha_k>0 .$$
--   Then:
--
--   1. $\gamma_k>0$ for every $k$;
--   2. for every upper bound $L$ of $(L_k)$, in particular $L=\sup_k L_k$ when it is finite, $\alpha_k\ge\sqrt{\min\{\gamma_0,\mu\}/L}$ for every $k$;
--   3. for every $k\ge1$,
--   $$\prod_{i=0}^{k-1}\frac{1}{1+\alpha_i}\le 4\left(2+\sum_{i=0}^{k-1}\sqrt{\frac{\gamma_0}{L_i}}\right)^{-2};$$
--   4. for every upper bound $L$ of $(L_k)$ and every $k\ge1$,
--   $$\prod_{i=0}^{k-1}\frac{1}{1+\alpha_i}\le\left(1+\sqrt{\frac{\min\{\gamma_0,\mu\}}{L}}\right)^{-k};$$
--   5. if $\mu=0$, then for every $k\ge1$,
--   $$\prod_{i=0}^{k-1}\frac{1}{1+\alpha_i}\ge\left(1+\sum_{i=0}^{k-1}\sqrt{\frac{\gamma_0}{L_i}}\right)^{-2}.$$
--
--   Items 3 and 4 are the paper's single bound by the minimum of the two expressions. The lemma converts the one-step contraction $\mathcal L_{k+1}\le\mathcal L_k/(1+\alpha_k)$ into explicit sublinear and linear rates, uniformly over the parameter choices used in §§5 and 7.
--
--   **Formalization Note.** The paper sets $L:=\sup_{k}L_k$. A real supremum of an unbounded sequence has no meaning in $\mathbb R$, so items 2 and 4 are stated for every real upper bound $L$ of $(L_k)$; since both conclusions weaken as $L$ grows, this is equivalent to the statement with the supremum whenever it is finite, and item 3, which does not involve $L$, is stated without any boundedness. The negative powers are integer powers of positive reals. The paper omits the proof ("Similarly, …").
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Lemma B.2, pp. 38–39

import Mathlib

namespace NAGFlow.PredCorr

/-- Lemma B.2 (Luo & Chen, arXiv:1909.03145v4, pp. 38–39). Let `γ₀ > 0`, `μ ≥ 0`, and let `(L_k)` be a
sequence of positive reals with `L_k ≥ μ`. Let `(α_k, γ_k)` satisfy
`γ_{k+1} = γ_k + α_k(μ − γ_{k+1})` and `L_kα_k² = γ_k(1 + α_k)`, `α_k > 0`, for every `k`. Then

1. `γ_k > 0` for every `k`;
2. for every upper bound `L` of `(L_k)` (in particular `L = sup_k L_k`), `α_k ≥ √(min{γ₀, μ}/L)`;
3. for every `k ≥ 1`, `∏_{i<k} 1/(1 + α_i) ≤ 4(2 + Σ_{i<k} √(γ₀/L_i))^{−2}`;
4. for every upper bound `L` of `(L_k)` and every `k ≥ 1`,
   `∏_{i<k} 1/(1 + α_i) ≤ (1 + √(min{γ₀, μ}/L))^{−k}`;
5. if `μ = 0`, then for every `k ≥ 1`, `∏_{i<k} 1/(1 + α_i) ≥ (1 + Σ_{i<k} √(γ₀/L_i))^{−2}`.

Items 3 and 4 together are the page's `∏ ≤ min{…, …}`. -/
theorem lemma_B_2 (μ : ℝ) (α γ Ls : ℕ → ℝ) (hγ0 : 0 < γ 0) (hμ : 0 ≤ μ)
    (hLpos : ∀ k, 0 < Ls k) (hLmu : ∀ k, μ ≤ Ls k)
    (hγ : ∀ k, γ (k + 1) = γ k + α k * (μ - γ (k + 1)))
    (hα : ∀ k, Ls k * α k ^ 2 = γ k * (1 + α k)) (hαpos : ∀ k, 0 < α k) :
    (∀ k, 0 < γ k) ∧
      (∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k, Real.sqrt (min (γ 0) μ / L) ≤ α k) ∧
      (∀ k : ℕ, 1 ≤ k →
        ∏ i ∈ Finset.range k, 1 / (1 + α i) ≤
          4 * (2 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) ^ (-2 : ℤ)) ∧
      (∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k : ℕ, 1 ≤ k →
        ∏ i ∈ Finset.range k, 1 / (1 + α i) ≤
          (1 + Real.sqrt (min (γ 0) μ / L)) ^ (-(k : ℤ))) ∧
      (μ = 0 → ∀ k : ℕ, 1 ≤ k →
        (1 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) ^ (-2 : ℤ) ≤
          ∏ i ∈ Finset.range k, 1 / (1 + α i)) := by sorry

end NAGFlow.PredCorr
