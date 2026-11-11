-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_proposition_6_2
-- name    : KXorTPCA.Reduction.proposition_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:50.650536+00:00
-- url     : https://prove2.me/theorems/4c789198-1c0d-4c55-97a7-13ebf5285ef7
-- title:
--   Proposition 6.2 — fixed-sample and Poissonized models are computationally equivalent, preserving x
-- statement:
--   For every noise model (k-XOR or k-Gauss), every index space ($k$-sets, FULL, asymm) and every sampling rule (with or without replacement), every $k\ge1$, $\rho\in[0,1]$ and $\eta\in\mathbb R$, the fixed-sample model $k$-model$^\star_{\rho,\eta}(n)$ (with $\lfloor m\rfloor$ samples) and its Poissonized variant $k$-model$^{\star,\mathrm{Pois}}_{\rho,\eta}(n)$ (with $\mathrm{Pois}(m)$ samples), $m=n^{k(1+\rho)/2}$, are computationally equivalent:
--
--   $$k\text{-model}^{\star}_{\rho,\eta}(n)\ \rightleftarrows\ k\text{-model}^{\star,\mathrm{Pois}}_{\rho,\eta}(n),$$
--
--   by polynomial-time average-case reductions (Definition C.6) for both detection and recovery in both directions, which keep the dimension and preserve $x$.
--
--   Differences from the source:
--   - reading: "$\star\subseteq\{\text{FULL/asymm},\text{wor}\}$" → every combination of index space and sampling; reason: "FULL/asymm" means at most one of the two.
--   - reading: unstated parameter range → $k\ge1$, $\rho\in[0,1]$, $\eta\in\mathbb R$; reason: the proposition states no range; §6.1 focuses on $\rho\ge0$.
--   - reading: "poly(n)-time average-case reductions for both detection and recovery" → the mission's Definition C.6; reason: Definitions C.5/C.6 leave these choices open.
--   - reading: "preserve the secret signal vector $x$ precisely" → $n'_i=n_i$ and $x'=x$; reason: literal meaning.
--   - reading: fixed sample count $m=n^{k(1+\rho)/2}$ → $\lfloor m\rfloor$ samples; reason: $m$ is real.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 23 (PDF 26), Proposition 6.2

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

namespace KXorTPCA.Reduction

theorem proposition_6_2 :
    ∀ (nz : Noise) (idx : IndexSpace) (smp : Sampling) (k : ℕ), 1 ≤ k →
    ∀ ρ η : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      CompEquiv (kModel ⟨nz, .fixed, idx, smp⟩ k) (ρ, η)
        (kModel ⟨nz, .pois, idx, smp⟩ k) (ρ, η) sameDims prefixSig := by sorry

end KXorTPCA.Reduction
