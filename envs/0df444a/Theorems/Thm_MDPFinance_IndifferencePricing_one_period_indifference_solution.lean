-- Prove2me | Theorems.Thm_MDPFinance_IndifferencePricing_one_period_indifference_solution
-- name    : MDPFinance.IndifferencePricing.one_period_indifference_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:10:32.23052+00:00
-- url     : https://prove2.me/theorems/8ac4627c-6167-46b2-9588-4cc38ac2f00c
-- title:
--   Theorem 4.9.2 — explicit one-period indifference price
-- statement:
--   With $q:=(1-d)/(u-d)$, $\tilde h(s_1,\hat s_1):=e^{\gamma h(s_1,\hat s_1)}$,
--   $h_u(s,\hat s):=p_1\tilde h(su,\hat s\hat u)+p_2\tilde h(su,\hat s\hat d)$,
--   $h_d(s,\hat s):=p_3\tilde h(sd,\hat s\hat u)+p_4\tilde h(sd,\hat s\hat d)$: a) $V_0^H(x,s,\hat
--   s) = -e^{-\gamma x}\big(h_u(s,\hat s)/q\big)^q\big(h_d(s,\hat s)/(1-q)\big)^{1-q}$;
--   b) the indifference price is
--   $$v_0(H,s,\hat s) = \frac{q}{\gamma}\log\frac{h_u(s,\hat s)}{p_1+p_2} +
--   \frac{1-q}{\gamma}\log\frac{h_d(s,\hat s)}{p_3+p_4}.$$
--
--   This is the base case of the chapter's indifference-pricing theory: a fully explicit price in
--   the simplest (one-period, four-atom) incomplete market, obtained by directly minimizing the
--   convex one-variable objective in Eq. (4.37) and reading off the indifference price from
--   Definition 4.9.1's defining equation.
--
--   **Formalization Note.** Part b) is stated by asserting that the printed formula *satisfies*
--   `IsIndifferencePrice` (Definition 4.9.1's equation), not by defining $v_0$ as that formula, so
--   that proving this item requires deriving the formula from the definition, not restating it.
--
--   **Moderation note.** The claim $H=h(S_1,\hat S_1)$ is nonnegative, as in the section's setup (p. 134-135), and the statement is made for $s,\hat s>0$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 136, PDF 150, Theorem 4.9.2

import Mathlib
import Definitions.Def_MDPFinance_IndifferencePricing_OnePeriodMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.IndifferencePricing

/-- Theorem 4.9.2 (Bäuerle–Rieder, p. 136, PDF 150). For the one-period financial market it holds:
a) The solution of problem (4.37) is `V_0^H(x,s,ŝ) = -e^{-γx}(h_u(s,ŝ)/q)^q(h_d(s,ŝ)/(1-q))^{1-q}`.
b) The indifference price of `H` is `v0(H,s,ŝ) = (q/γ)log(h_u(s,ŝ)/(p1+p2)) +
((1-q)/γ)log(h_d(s,ŝ)/(p3+p4))`. The claim `H = h(S1,Ŝ1)` is nonnegative (p. 135: "a
non-negative random variable `H`"). -/
theorem one_period_indifference_solution {Ω : Type*} [MeasurableSpace Ω]
    (M : OnePeriodIndifferenceMarket Ω) (h : ℝ → ℝ → ℝ) (hh : ∀ s1 ŝ1, 0 ≤ h s1 ŝ1)
    (x s ŝ : ℝ) (hs : 0 < s) (hŝ : 0 < ŝ) :
    M.V0 h x s ŝ = -Real.exp (-M.γ * x) * (M.hu h s ŝ / M.qrn) ^ M.qrn *
        (M.hd h s ŝ / (1 - M.qrn)) ^ (1 - M.qrn) ∧
      M.IsIndifferencePrice h s ŝ
        (M.qrn / M.γ * Real.log (M.hu h s ŝ / (M.p1 + M.p2)) +
          (1 - M.qrn) / M.γ * Real.log (M.hd h s ŝ / (M.p3 + M.p4))) := by sorry

end MDPFinance.IndifferencePricing
