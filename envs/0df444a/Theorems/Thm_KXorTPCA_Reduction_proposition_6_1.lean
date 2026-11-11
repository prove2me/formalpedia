-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_proposition_6_1
-- name    : KXorTPCA.Reduction.proposition_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:38.883759+00:00
-- url     : https://prove2.me/theorems/37b02971-089d-4882-b4d3-071c357c878b
-- title:
--   Proposition 6.1 — k-XOR⋆ and k-Gauss⋆ are computationally equivalent, preserving x
-- statement:
--   For every choice of the number of samples (fixed or Poissonized), of the index space ($k$-sets, FULL multisets, or asymm ordered tuples) and of the sampling (with or without replacement), every order $k\ge1$ and all parameters $\rho\in[0,1]$, $\eta\in\mathbb R$, the discrete model $k$-XOR$^\star_{\rho,\eta}(n)$ and its Gaussian analog $k$-Gauss$^\star_{\rho,\eta}(n)$ are computationally equivalent:
--
--   $$k\text{-XOR}^\star_{\rho,\eta}(n)\ \rightleftarrows\ k\text{-Gauss}^\star_{\rho,\eta}(n),$$
--
--   that is, there are polynomial-time average-case reductions (Definition C.6) for both detection and recovery in both directions, which keep the dimension and preserve the secret signal vector: $x'=x$.
--
--   The two noise models (multiplicative Rademacher, additive Gaussian) are therefore interchangeable in every result of the paper.
--
--   Differences from the source:
--   - reading: "$\star\subseteq\{\text{Pois},\text{FULL/asymm},\text{wor}\}$" → every combination of the sample count, index space and sampling options; reason: "FULL/asymm" means at most one of the two.
--   - reading: unstated parameter range → $k\ge1$, $\rho\in[0,1]$ (§6.1: "we focus on the case $\rho\ge0$"), $\eta\in\mathbb R$; reason: the proposition states no range.
--   - reading: "poly(n)-time average-case reductions for both detection and recovery" → the mission's Definition C.6 (one reduction and one recovery map for both tasks, the same sequences, the standard losses with loss map $t\mapsto t+\varepsilon_i$); reason: Definitions C.5/C.6 leave these choices open.
--   - reading: "preserve the secret signal vector $x$ precisely" → $n'_i=n_i$ and $x'=x$; reason: literal meaning.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 23 (PDF 26), Proposition 6.1

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

namespace KXorTPCA.Reduction

theorem proposition_6_1 :
    ∀ (cnt : Count) (idx : IndexSpace) (smp : Sampling) (k : ℕ), 1 ≤ k →
    ∀ ρ η : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      CompEquiv (kModel ⟨.xor, cnt, idx, smp⟩ k) (ρ, η)
        (kModel ⟨.gauss, cnt, idx, smp⟩ k) (ρ, η) sameDims prefixSig := by sorry

end KXorTPCA.Reduction
