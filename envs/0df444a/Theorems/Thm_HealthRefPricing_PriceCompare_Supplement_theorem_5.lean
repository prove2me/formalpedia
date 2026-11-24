-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_Supplement_theorem_5
-- name    : HealthRefPricing.PriceCompare.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:40:42.463906+00:00
-- url     : https://prove2.me/theorems/7ecea91b-b203-4d73-acb5-6d97141703de
-- title:
--   Theorem 5, Appendix p. 2 — RV equilibrium existence and the unique status-consistent solution of (11)
-- statement:
--   Let $\lambda\in(0,1]$ be the patient cost share. Under the published standing assumptions and Assumption 5 at $\lambda$, an RV Nash equilibrium exists. Fix any such equilibrium $p$, and let $\mathcal N=\{j:p_j>p^*\}$ be its non-value-based providers. Write $S^{RV}_j(p)$ for the published multinomial-logit share with out-of-pocket $o^{RV}_j(p)=\lambda\min\{p_j,p^*\}+\max\{0,p_j-p^*\}$. Then
--
--   $$\begin{aligned}
--   1-\gamma(p_j-c)(1-S^{RV}_j(p))&=0 &&j\in\mathcal N,\\
--   1-\gamma\lambda(\hat p_j-c)(1-S^{RV}_j(\hat p_j,p_{-j}))&=0 &&j\notin\mathcal N,\\
--   p_j&=\min\{\hat p_j,p^*\} &&j\notin\mathcal N.
--   \end{aligned}\tag{11}$$
--
--   For every value-based provider there is an auxiliary price $\hat p_j$ satisfying the last two equations. Moreover, any real price vector $q$ satisfying the same system, with auxiliary prices where necessary and $q_j>p^*$ for $j\in\mathcal N$, equals $p$. The minimum equation makes $q_j\le p^*$ for the other providers.
--
--   The parameters are population $m>0$, sensitivity $\gamma>0$, common cost $c\ge0$, attributes $a_1\le a_2$, outside-option utility $u_0$, and reference price $p^*$. This companion theorem characterizes RV prices for a given equilibrium status set; it is not used in the proof of the Proposition 5 goal.
--
--   **Formalization Note** Providers use `Fin 2`: index 0 is provider 1 and index 1 provider 2. The published Standing also includes $\tilde c<c$, although RV does not use the co-payment. Neither auxiliary-price uniqueness nor uniqueness across different status sets is asserted. The auxiliaries are evaluated using the literal RV rule, including when they exceed $p^*$. Equilibrium means pure Nash equilibrium, not merely a stationary solution.
--
--   Differences from the source:
--   - reading: given the set of non-value-based providers N, equilibrium prices are the unique solution of (11) → for each actual equilibrium p, take N={j | ps<pj}; uniqueness is among solutions with that same status set; reason: N is a classification of prices, not an arbitrary unrelated input; the min equation enforces value-based status and non-value-based solutions explicitly stay above ps.
--   - reading: Theorem 5 describes prices at equilibrium, after stating Assumption 5 guarantees existence → an RV Nash equilibrium exists, and every equilibrium satisfies all three rows of (11); reason: Appendix C.1 (PDF 35) explicitly introduces Assumption 5 as guaranteeing a pure Nash equilibrium; the proof notice on PDF 45 refers to the analogous existence arguments.
--   - encoding: best-response share limit notation and two providers with above-cost prices → Assumption5 requires existing selections and convergence along every selection; Fin 2 and all real prices with published Standing; reason: the limit is not an unchecked default value, index 0 is provider 1, and nonpositive-profit prices ≤c cannot be equilibrium prices; inherited positivity and nonnegative-cost conventions match the economic setting.
--   - reading: the auxiliary p-hat in (11) is evaluated in the RV share → existential auxiliary own prices with the literal oopRV at the substituted profile, even above ps; reason: this transcribes the printed RV superscript without replacing it by a VP share; p-hat is not a second strategy variable and actual value-based prices are its minimum with ps.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), Appendix p. 2 (PDF 35), Theorem 5, system (11), Assumption 5; proof notice, Appendix p. 12 (PDF 45)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Supplement_Assumption5

namespace HealthRefPricing.PriceCompare.Supplement

/-- Theorem 5: existence, system (11), and uniqueness for the equilibrium's given status set.
Auxiliary prices for value-based providers are existential witnesses, not game strategies. -/
theorem theorem_5 (P : Params) (hS : P.Standing) (lam : ℝ)
    (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) (hA5 : Assumption5 P lam) :
    (∃ p : Fin 2 → ℝ, IsEqRV P lam p) ∧
    ∀ p : Fin 2 → ℝ, IsEqRV P lam p →
      (∀ j : Fin 2, P.ps < p j →
        1 - P.γ * (p j - P.c) * (1 - share P (oopRV P lam p) j) = 0) ∧
      (∀ j : Fin 2, p j ≤ P.ps → ∃ phat : ℝ,
        1 - P.γ * lam * (phat - P.c) *
          (1 - share P (oopRV P lam (vs j phat (p (1 - j)))) j) = 0 ∧
        p j = min phat P.ps) ∧
      (∀ q : Fin 2 → ℝ,
        (∀ j : Fin 2, P.ps < p j → P.ps < q j ∧
          1 - P.γ * (q j - P.c) * (1 - share P (oopRV P lam q) j) = 0) →
        (∀ j : Fin 2, p j ≤ P.ps → ∃ qhat : ℝ,
          1 - P.γ * lam * (qhat - P.c) *
            (1 - share P (oopRV P lam (vs j qhat (q (1 - j)))) j) = 0 ∧
          q j = min qhat P.ps) → q = p) := by sorry

end HealthRefPricing.PriceCompare.Supplement
