-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_2
-- name    : OfflineCensoredPricing.Identifiability.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:37.118071+00:00
-- url     : https://prove2.me/theorems/04668958-4123-4380-99eb-88dc41273181
-- title:
--   Proposition 2, p. 13 — closed forms Rmax = 1{p<p̃}R_Fξ + 1{p≥p̃}R1 and Rmin = 1{p<p̃}R_Fξ + 1{p≥p̃}R2, with max and min attained
-- statement:
--   Fix an instance satisfying the standing assumptions, with ambiguity set $\mathcal F$, observable boundary $\lambda$, $\gamma = \mathbb P[\xi < \lambda]$ and $\tilde p = (\lambda - y)/b$. For any $p \in [\underline p,\bar p]$,
--   $$R_{\max}(p) = \mathbb 1_{\{p<\tilde p\}} R_{F_\xi}(p) + \mathbb 1_{\{p\ge\tilde p\}} R_1(p), \qquad R_{\min}(p) = \mathbb 1_{\{p<\tilde p\}} R_{F_\xi}(p) + \mathbb 1_{\{p\ge\tilde p\}} R_2(p),$$
--   where $R_1(p) = p(-\gamma bp + \mathbb E_{F_\xi}[\min\{\xi,\lambda\}] + (1-\gamma)(y-\lambda))$ and $R_2(p) = p(-bp + \mathbb E_{F_\xi}[\min\{\xi,\lambda\}])$. Moreover the maximum and the minimum of $R_F(p)$ over $F \in \mathcal F$ are attained.
--
--   The closed forms do not involve the unobservable part of $F_\xi$ on $[\lambda,\infty)$, which is what makes the optimistic and pessimistic revenues learnable from censored data.
--
--   **Formalization Note** $R_{\max}$ and $R_{\min}$ are defined as the supremum and infimum of $R_F(p)$ over the ambiguity set; the statement asserts that the closed-form value is the greatest (resp. least) element of $\{R_F(p) : F \in \mathcal F\}$ and equals $R_{\max}(p)$ (resp. $R_{\min}(p)$). Attainment is shown in the proof (Appendix C.1, p. 36), which exhibits the extremal distributions.
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 13, Proposition 2 (proof Appendix C.1, pp. 35–36)

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Proposition 2** (p. 13). For any `q ∈ [p̲, p̄]`,
`R_max(q) = 1{q < p̃} R_{F_ξ}(q) + 1{q ≥ p̃} R₁(q)` and `R_min(q) = 1{q < p̃} R_{F_ξ}(q) + 1{q ≥ p̃} R₂(q)`,
where `R₁(q) = q(−γbq + E_{F_ξ}[min{ξ, λ}] + (1 − γ)(y − λ))` and `R₂(q) = q(−bq + E_{F_ξ}[min{ξ, λ}])`.
The maximum and the minimum over the ambiguity set are attained (proof in Appendix C.1, p. 36). -/
theorem proposition_2 {K : ℕ} (I : Instance K) (hI : I.Standing) (q : ℝ)
    (hq : q ∈ Icc I.plo I.phi) :
    IsGreatest ((fun μ => RF I μ q) '' Amb I)
        (if q < pTilde I then RF I I.μξ q else R1 I q) ∧
      IsLeast ((fun μ => RF I μ q) '' Amb I)
        (if q < pTilde I then RF I I.μξ q else R2 I q) ∧
      Rmax I q = (if q < pTilde I then RF I I.μξ q else R1 I q) ∧
      Rmin I q = (if q < pTilde I then RF I I.μξ q else R2 I q) := by sorry

end OfflineCensoredPricing.Identifiability
