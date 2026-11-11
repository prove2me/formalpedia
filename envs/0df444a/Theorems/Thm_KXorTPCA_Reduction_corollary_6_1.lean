-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_corollary_6_1
-- name    : KXorTPCA.Reduction.corollary_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:51.137527+00:00
-- url     : https://prove2.me/theorems/fed44ecc-1ad8-4417-98d6-9c4c9ce3731e
-- title:
--   Corollary 6.1 — k-TensorPCA_η is computationally equivalent to k-model^{⋆,FULL}_{ρ=1,η}; its distinct-index version to k-model^⋆_{ρ=1,η}
-- statement:
--   Let $k\ge1$ and $\eta>0$, and let $k$-TensorPCA$_\eta(n)$ be the Tensor PCA model $\delta x^{\otimes k}+G$, $\delta=n^{-k/4-\eta/2}$, $G$ a symmetric tensor of $N(0,1)$ (Eq. (19)).
--
--   1. For every noise model, every sample count rule and every sampling rule, $k$-TensorPCA$_\eta(n)$ is computationally equivalent to the FULL model $k$-model$^{\star,\mathrm{FULL}}_{\rho=1,\eta}(n)$ (in particular to $k$-Gauss$^{\mathrm{FULL}}_{\rho=1,\eta}(n)$).
--   2. The model that observes only the distinct-index entries of Eq. (19) is computationally equivalent to $k$-model$^\star_{\rho=1,\eta}(n)$ for every noise model, sample count rule and sampling rule, with index space $k$-sets or asymm (in particular to $k$-Gauss$_{\rho=1,\eta}(n)$).
--
--   Equivalence means polynomial-time average-case reductions (Definition C.6) for both detection and recovery in both directions.
--
--   Differences from the source:
--   - reading: part 1, "$\star\subseteq\{\text{Pois},\text{asymm},\text{wor}\}$" together with FULL → sample count and sampling free, index space FULL; reason: asymm and FULL are exclusive options of choice (3).
--   - reading: part 2, "$\star\subseteq\{\text{Pois},\text{asymm},\text{wor}\}$" → sample count and sampling free, index space $k$-sets or asymm; reason: literal meaning.
--   - reading: Tensor PCA in Definition C.6's parameter sequences → $\delta=n^{-k\rho/4-\eta/2}$ with $\rho\to1$; reason: Definition C.6 needs a two-parameter family; at $\rho=1$ it is $k$-TensorPCA$_\eta$.
--   - reading: "observes only distinct-index entries" → the entries with a repeated index are replaced by $0$; reason: encoding of unobserved entries.
--   - reading: "computationally equivalent" → the mission's Definition C.6 both ways; reason: Definitions C.5/C.6 leave these choices open.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), pp. 24–25 (PDF 27–28), Corollary 6.1, Eq. (19)

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

namespace KXorTPCA.Reduction

theorem corollary_6_1 :
    ∀ k : ℕ, 1 ≤ k → ∀ η : ℝ, 0 < η →
      (∀ (nz : Noise) (cnt : Count) (smp : Sampling),
        CompEquiv (tpcaFam k false) (1, η) (kModel ⟨nz, cnt, .full, smp⟩ k) (1, η)
          anyDims anySig) ∧
      (∀ (nz : Noise) (cnt : Count) (idx : IndexSpace) (smp : Sampling),
        (idx = .subsets ∨ idx = .asymm) →
        CompEquiv (tpcaFam k true) (1, η) (kModel ⟨nz, cnt, idx, smp⟩ k) (1, η)
          anyDims anySig) := by sorry

end KXorTPCA.Reduction
