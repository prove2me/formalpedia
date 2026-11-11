-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_proposition_6_6
-- name    : KXorTPCA.Reduction.proposition_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:51.18931+00:00
-- url     : https://prove2.me/theorems/e7dc2432-956d-4355-928c-c7e4855f123a
-- title:
--   Proposition 6.6 — at ρ = 1, sampling with and without replacement are computationally equivalent, preserving x
-- statement:
--   For every noise model, every sample count rule, every index space ($k$-sets, FULL, asymm), every $k\ge1$ and every $\eta>0$, the models $k$-model$^\star_{\rho=1,\eta}(n)$ (with replacement) and $k$-model$^{\star,\mathrm{wor}}_{\rho=1,\eta}(n)$ (without replacement) are computationally equivalent:
--
--   $$k\text{-model}^{\star}_{1,\eta}(n)\ \rightleftarrows\ k\text{-model}^{\star,\mathrm{wor}}_{1,\eta}(n),$$
--
--   by polynomial-time average-case reductions (Definition C.6) for both detection and recovery in both directions, which keep the dimension and preserve $x$.
--
--   Differences from the source:
--   - reading: "$\star\subseteq\{\text{Pois},\text{FULL/asymm}\}$" → every combination of sample count and index space; reason: "FULL/asymm" means at most one of the two.
--   - reading: without replacement with more requested samples than index objects → all index objects once, in random order; reason: Fig. 6 does not say; §12 reads $k$-Gauss$^{\mathrm{wor}}_{\rho=1}$ as one observation per index set.
--   - reading: "poly(n)-time average-case reductions for both detection and recovery" → the mission's Definition C.6; reason: Definitions C.5/C.6 leave these choices open.
--   - reading: "preserve the secret signal vector $x$ precisely" → $n'_i=n_i$ and $x'=x$; reason: literal meaning.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 24 (PDF 27), Proposition 6.6; p. 64 (PDF 67), §12 (k-Gauss^wor_{ρ=1})

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

namespace KXorTPCA.Reduction

theorem proposition_6_6 :
    ∀ (nz : Noise) (cnt : Count) (idx : IndexSpace) (k : ℕ), 1 ≤ k → ∀ η : ℝ, 0 < η →
      CompEquiv (kModel ⟨nz, cnt, idx, .wr⟩ k) (1, η)
        (kModel ⟨nz, cnt, idx, .wor⟩ k) (1, η) sameDims prefixSig := by sorry

end KXorTPCA.Reduction
