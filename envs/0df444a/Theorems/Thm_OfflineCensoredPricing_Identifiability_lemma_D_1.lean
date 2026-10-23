-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_D_1
-- name    : OfflineCensoredPricing.Identifiability.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:19.981054+00:00
-- url     : https://prove2.me/theorems/4db0c306-3904-4971-914d-929fb91acae4
-- title:
--   Lemma D.1, p. 45 — |R̂(p) − R(p)| ≤ 3p̄²|b̂ − b| + α for all 0 ≤ p ≤ max{min{p̂~, p̃, p̄}, 0}, w.p. ≥ 1 − 2Ke^{−Nα²/((y+b̄p̄)²p̄²)}
-- statement:
--   Fix an instance satisfying the standing assumptions, with data size $N = \min_i N_i$. Let $R = R_{F_\xi}$ be the true expected revenue, $\tilde p = (\lambda - y)/b$, and let $\hat R$, $\hat b$, $\hat{\tilde p}$ be the empirical revenue, sensitivity estimate and estimated threshold computed by D2ACD from the censored sales. For any $\alpha > 0$, with probability at least $1 - 2Ke^{-N\alpha^2/((y+\bar b\bar p)^2\bar p^2)}$,
--   $$\big|\hat R(p) - R(p)\big| \le 3\bar p^2|\hat b - b| + \alpha \quad\text{for all } 0 \le p \le \max\{\min\{\hat{\tilde p}, \tilde p, \bar p\}, 0\}.$$
--
--   Below both thresholds no censoring distorts the empirical revenue, so it tracks the true revenue up to the error in $\hat b$. This is one of the two technical lemmas behind Lemma 2.
--
--   **Formalization Note** The failure event is $\{\exists p,\ 0 \le p \le \max\{\min\{\hat{\tilde p},\tilde p,\bar p\},0\},\ |\hat R(p) - R(p)| > 3\bar p^2|\hat b - b| + \alpha\}$, whose outer probability is bounded. Here $\hat R$ uses the data of the pair $\hat i^*$ selected by D2ACD.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 45, Lemma D.1 (proof Appendix D.4, pp. 51–53)

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Lemma D.1** (Convergence of empirical revenue, p. 45). For any `α > 0`, with probability at least
`1 − 2K e^{−Nα²/((y + b̄p̄)² p̄²)}`, `|R̂(q) − R(q)| ≤ 3p̄² |b̂ − b| + α` for all
`0 ≤ q ≤ max{min{p̂~, p̃, p̄}, 0}`, where `R = R_{F_ξ}` is the true expected revenue and `R̂`, `b̂`, `p̂~` are
computed by D2ACD from the censored data. -/
theorem lemma_D_1 {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) (Nv : Fin K → ℕ) {α : ℝ}
    (hα : 0 < α) :
    dataLaw I Nv {ω | ∃ q : ℝ, 0 ≤ q ∧
        q ≤ max (min (min (pTildeHat I.toPublic (sales I ω)) (pTilde I)) I.phi) 0 ∧
        3 * I.phi ^ 2 * |bHat I.toPublic (sales I ω) - I.b| + α <
          |RHat I.toPublic (sales I ω) q - RF I I.μξ q|} ≤
      ENNReal.ofReal (2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 /
        ((I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2)))) := by sorry

end OfflineCensoredPricing.Identifiability
