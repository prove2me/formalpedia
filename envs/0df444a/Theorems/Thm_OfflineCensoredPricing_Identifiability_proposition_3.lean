-- Prove2me | Theorems.Thm_OfflineCensoredPricing_Identifiability_proposition_3
-- name    : OfflineCensoredPricing.Identifiability.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:34.900831+00:00
-- url     : https://prove2.me/theorems/baba6d5e-854a-4e69-910a-8a5c33459ed8
-- title:
--   Proposition 3, p. 13 — p*_min ≤ p*_F ≤ p*_max for every F in the ambiguity set; p*_max, p*_min are the largest maximizers of Rmax, Rmin
-- statement:
--   Fix an instance satisfying the standing assumptions. The optimistic price $p^*_{\max}$ is the largest maximizer of $R_{\max}$ on $[\underline p,\bar p]$, the pessimistic price $p^*_{\min}$ is the largest maximizer of $R_{\min}$ on $[\underline p,\bar p]$ (both maximizers exist), and for any c.d.f. $F$ in the ambiguity set $\mathcal F$,
--   $$p^*_{\min} \le p^*_F \le p^*_{\max}.$$
--
--   The optimal price of every distribution consistent with the data is sandwiched between the optimistic and pessimistic prices; when the two coincide, every $F \in \mathcal F$ has the same optimal price, which is the intuition behind Theorem 1.
--
--   **Formalization Note** The first two clauses (existence of the largest maximizers) are part of the statement because $p^*_{\max}$ and $p^*_{\min}$ are defined as suprema of the sets of maximizers; they are established in the paper's proof (Appendix C.3, last paragraph, p. 39: $p^*_{\max} = \mathrm{Proj}(p^\dagger_{\max}, [\underline p,\bar p])$).
-- source:
--   Bu, Simchi-Levi & Wang, SSRN 3619625 (PDF of 2021-08-23), p. 13, Proposition 3 (proof Appendix C.3, pp. 37–39)

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model

namespace OfflineCensoredPricing.Identifiability

open MeasureTheory Set

/-- **Proposition 3** (p. 13). For any `F ∈ 𝓕`, `p*_min ≤ p*_F ≤ p*_max`. The statement also records
that `p*_max` and `p*_min` are the largest maximizers of `R_max` and `R_min` on `[p̲, p̄]` (shown in
the proof, Appendix C.3, pp. 37–39). -/
theorem proposition_3 {K : ℕ} (I : Instance K) (hI : I.Standing) :
    IsGreatest {q ∈ Icc I.plo I.phi | ∀ q' ∈ Icc I.plo I.phi, Rmax I q' ≤ Rmax I q} (pStarMax I) ∧
      IsGreatest {q ∈ Icc I.plo I.phi | ∀ q' ∈ Icc I.plo I.phi, Rmin I q' ≤ Rmin I q}
        (pStarMin I) ∧
      ∀ μ ∈ Amb I, pStarMin I ≤ pStar I μ ∧ pStar I μ ≤ pStarMax I := by sorry

end OfflineCensoredPricing.Identifiability
