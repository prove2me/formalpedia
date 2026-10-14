-- Prove2me | Theorems.Thm_NetFeePlatform_InteropDominance_proposition_6
-- name    : NetFeePlatform.InteropDominance.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:13.486056+00:00
-- url     : https://prove2.me/theorems/4c0ae405-e5b3-47cd-9de1-8cbb2377f65e
-- title:
--   Proposition 6, p. 23 — in a Logit duopoly, every equilibrium with a dominant share above 1/2 under higher interoperability is outsized by an equilibrium under lower interoperability
-- statement:
--   **Interoperability may mitigate dominance.** Consider two ex ante identical platforms with Logit demand and no outside option, marginal cost $c$, network-interaction value $\gamma>0$, and let $0\le\underline\lambda<\overline\lambda\le1$ be two degrees of interoperability. Assume moreover
--
--   $$\gamma(1-\underline\lambda)\le\frac{27}{8}.$$
--
--   Let $t$ be a Nash equilibrium in net fees under $\overline\lambda$ in which platform $j$ is dominant, $\overline n^j=n^j(t)>1/2$. Then there is a Nash equilibrium $t'$ under $\underline\lambda$ in which the same platform has an even larger share:
--
--   $$n^j(t')>n^j(t).$$
--
--   This is the paper's statement that interoperability may mitigate dominance: whenever a higher degree of interoperability supports an equilibrium with a dominant platform, a lower degree supports an equilibrium in which that platform is even larger.
--
--   **Formalization Note** The paper assumes $\gamma>0$ and $\lambda\in[0,1]$. The hypothesis $\gamma(1-\underline\lambda)\le 27/8$ is added: the paper's proof constructs a zero of $\zeta(\cdot\,;\underline\lambda)$, which satisfies both first-order conditions, and calls it an equilibrium; the paper establishes that the first-order condition is sufficient for a best response only when $\gamma(1-\lambda)\le 27/8$ (Appendix E.1.3 with (36), the $3.375$ of Proposition 2′). Equilibrium is the global Nash condition over every unilateral deviation. The dominant platform's index $j$ is the same in both equilibria (the platforms are ex ante identical; the page calls it platform 1).
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 23, Proposition 6; proof pp. 51–52, Appendix E.2

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropDominance

theorem proposition_6 (c γ lamLo lamHi : ℝ) (hγ : 0 < γ) (hlo : 0 ≤ lamLo) (hlt : lamLo < lamHi)
    (hhi : lamHi ≤ 1) (hreg : γ * (1 - lamLo) ≤ 27 / 8)
    (t : Fin 2 → ℝ) (ht : NetFeePlatform.Competition.IsEquilibrium 0 c γ lamHi t) (j : Fin 2) (hdom : 1 / 2 < NetFeePlatform.Competition.demand 0 t j) :
    ∃ t' : Fin 2 → ℝ, NetFeePlatform.Competition.IsEquilibrium 0 c γ lamLo t' ∧ NetFeePlatform.Competition.demand 0 t j < NetFeePlatform.Competition.demand 0 t' j := by sorry

end NetFeePlatform.InteropDominance
