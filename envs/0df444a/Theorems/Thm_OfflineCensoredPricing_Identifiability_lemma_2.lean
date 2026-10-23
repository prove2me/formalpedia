-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_2
-- name    : OfflineCensoredPricing.Identifiability.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:20.823996+00:00
-- url     : https://prove2.me/theorems/a61fed11-9f4d-4d4d-a50f-1f6929fb2489
-- title:
--   Lemma 2, p. 20 — sup over [p̲, p̄] of |R̂max − Rmax| and |R̂min − Rmin| are ≤ α with probability ≥ 1 minus four explicit exponential terms
-- statement:
--   Fix an instance satisfying the standing assumptions, with data size $N = \min_i N_i$, and write $\bar\lambda = \max_i\{y_i + \bar bp_i\}$, $C_1 = 5\bar p^2 + \frac{(2y + 3\bar b\bar p + 2\bar\lambda)^2}{\underline b^2}$ and $C_2 = \bar p(y + \bar\lambda + \bar p\bar b)$. Let $\hat R_{\max}$, $\hat R_{\min}$ be the empirical optimistic and pessimistic revenues of D2ACD. For any $\alpha > 0$, $\sup_{p\in[\underline p,\bar p]}|\hat R_{\max}(p) - R_{\max}(p)| \le \alpha$ and $\sup_{p\in[\underline p,\bar p]}|\hat R_{\min}(p) - R_{\min}(p)| \le \alpha$ with probability at least
--   $$1 - 2Ke^{-\frac{N\alpha^2}{36(y+\bar b\bar p)^2\bar p^2}} - 2Ke^{-\frac{\frac1K\sum_{i=1}^K(p_i - \frac1K\sum_{j=1}^K p_j)^2\underline g^2}{36C_1^2}N\alpha^2} - 2Ke^{-\frac{N\alpha^2}{18C_2^2}} - 2Ke^{-\frac{N\alpha^2}{18\bar p^2\bar\lambda^2}}.$$
--
--   Uniform approximation of the two robust revenue curves is the estimation guarantee on which the performance of D2ACD (Theorems 2 and 3) rests.
--
--   **Formalization Note** The statement is made on the data assumption $\hat\gamma_i > 0$ for every $i$ (p. 10), inherited from Lemma 1: the outer probability of $\{\exists p\in[\underline p,\bar p],\ |\hat R_{\max}(p) - R_{\max}(p)| > \alpha \text{ or } |\hat R_{\min}(p) - R_{\min}(p)| > \alpha\} \cap \{\hat\gamma_i > 0\ \forall i\}$ is at most the four terms.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 20, Lemma 2 with the notation λ̄, C1, C2 stated before it (proof Appendix D.2, pp. 45–48)

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Lemma 2** (Convergence of empirical optimistic and pessimistic revenues, p. 20). With
`λ̄ = maxᵢ {yᵢ + b̄pᵢ}`, `C₁ = 5p̄² + (2y + 3b̄p̄ + 2λ̄)²/b̲²` and `C₂ = p̄(y + λ̄ + p̄b̄)`: for any `α > 0`,
`sup_{q ∈ [p̲, p̄]} |R̂_max(q) − R_max(q)| ≤ α` and `sup_{q ∈ [p̲, p̄]} |R̂_min(q) − R_min(q)| ≤ α` with
probability at least
`1 − 2Ke^{−Nα²/(36(y+b̄p̄)²p̄²)} − 2Ke^{−((1/K)∑ᵢ(pᵢ − (1/K)∑ⱼpⱼ)² g̲²/(36C₁²)) Nα²} − 2Ke^{−Nα²/(18C₂²)}
− 2Ke^{−Nα²/(18p̄²λ̄²)}`. Stated on the data assumption `γ̂ᵢ > 0` for all `i` (p. 10). -/
theorem lemma_2 {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) (Nv : Fin K → ℕ) {α : ℝ}
    (hα : 0 < α) :
    dataLaw I Nv {ω | ((∃ q ∈ Icc I.plo I.phi, α < |RHatMax I.toPublic (sales I ω) q - Rmax I q|) ∨
          (∃ q ∈ Icc I.plo I.phi, α < |RHatMin I.toPublic (sales I ω) q - Rmin I q|)) ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ≤
      ENNReal.ofReal
        (2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (36 * (I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2))) +
          2 * K * Real.exp (-(priceVar I.toPublic * I.g ^ 2 / (36 * C1 I ^ 2) *
            (Nmin Nv : ℝ) * α ^ 2)) +
          2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * C2 I ^ 2))) +
          2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2)))) := by sorry

end OfflineCensoredPricing.Identifiability
