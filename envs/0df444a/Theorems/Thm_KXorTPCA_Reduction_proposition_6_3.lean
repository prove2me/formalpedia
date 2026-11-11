-- Prove2me | Theorems.Thm_KXorTPCA_Reduction_proposition_6_3
-- name    : KXorTPCA.Reduction.proposition_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:24:42.705726+00:00
-- url     : https://prove2.me/theorems/e1019cfc-de58-459c-9e51-9c4b46c5614f
-- title:
--   Proposition 6.3 — a FULL (multiset) instance is equivalent to a collection of distinct-index instances of orders k, k − 2, k − 4, …
-- statement:
--   Fix $k\ge1$, $\rho\in[0,1]$, $\eta\ge0$, a noise model, a sample count rule and a sampling rule. Let $\rho_r=\min\{k\rho/(k-2r),1\}$. Then the FULL model and the collection of independent distinct-index instances sharing the secret $x$ (footnote 20),
--
--   $$k\text{-model}^{\star,\mathrm{FULL}}_{\rho,\eta}(n)\quad\text{and}\quad\big\{(k-2r)\text{-model}^{\star}_{\rho_r,\eta}(n)\big\}_{0\le r\le (k-1)/2},$$
--
--   are computationally equivalent: there are polynomial-time average-case reductions (Definition C.6) for both detection and recovery both ways, which keep the dimension and preserve $x$ exactly.
--
--   Differences from the source:
--   - generalization: $\eta\in\mathbb R_+$ → $\eta\ge0$; reason: $\mathbb R_+$ is read as $[0,\infty)$, which contains $(0,\infty)$.
--   - reading: $k\in\mathbb Z$ → $k\ge1$; reason: model orders are positive.
--   - reading: "a collection of independent $k$-model instances" → the collection model of the mission (components on independent tapes, interleaved cells, shared secret), with $(k+1)/2$ components $r=0,\dots,\lfloor (k-1)/2\rfloor$; reason: encoding of a collection.
--   - reading: "poly-time average-case reductions both ways" → the mission's Definition C.6 for both detection and recovery; reason: Definitions C.5/C.6 leave these choices open.
--   - reading: "preserve the input signal vector $x$ exactly" → $n'_i=n_i$, $x'=x$; reason: literal meaning.
-- source:
--   G. Bresler, A. Harbuzova, Average-Case Reductions for k-XOR and Tensor PCA, arXiv:2601.19016 (copy sha256 6ec029a7…), p. 23 (PDF 26), Proposition 6.3, footnote 20

import Mathlib
import Definitions.Def_KXorTPCA_Reduction_Reductions

namespace KXorTPCA.Reduction

theorem proposition_6_3 :
    ∀ (nz : Noise) (cnt : Count) (smp : Sampling) (k : ℕ), 1 ≤ k →
    ∀ ρ η : ℝ, 0 ≤ ρ → ρ ≤ 1 → 0 ≤ η →
      CompEquiv (kModel ⟨nz, cnt, .full, smp⟩ k) (ρ, η)
        (fun ρ η n => bundle (R := (k + 1) / 2) fun r =>
          kModel ⟨nz, cnt, .subsets, smp⟩ (k - 2 * (r : ℕ))
            (min ((k : ℝ) * ρ / ((k : ℝ) - 2 * (r : ℕ))) 1) η n)
        (ρ, η) sameDims prefixSig := by sorry

end KXorTPCA.Reduction
