-- Prove2me | Theorems.Thm_InsiderDonations_trader_foc
-- name    : InsiderDonations.trader_foc
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:38.674377+00:00
-- url     : https://prove2.me/theorems/f9f83d00-74c3-4e20-a4cc-d3eadbe317cf
-- title:
--   Appendix, proof of Proposition 1, p.A1 — trader $j$'s first-order condition
-- statement:
--   Fix a linear profile with pricing rule $P(y)=\alpha-\lambda y$, $\lambda>0$, under the standing assumptions. For trader $j$, firm value $v$, and the other agents' linear strategies (written $\hat x_k$, $\hat d_i$), trader $j$ chooses $x$ to maximize
--   $$
--   E\Big[\Big(\alpha-\lambda\Big(u+\omega\sum_{i=1}^m\hat d_i+\sum_{k\ne j}\hat x_k+x\Big)-v\Big)(1-\tau_c)\,x\Big],
--   $$
--   the expectation being over $u$ and the donors' motives. Then $x$ maximizes this expected utility if and only if
--   $$
--   x=\frac{\alpha-v}{2\lambda}-\frac{\omega\sum_{i=1}^mE[\hat d_i]}{2}-\frac{\sum_{k\ne j}\hat x_k}{2},
--   $$
--   where $E[\hat d_i]$ is donor $i$'s donation at $v$ averaged over her motive $\psi_i\sim N(\bar\psi,\sigma_\psi^2)$.
--
--   This is the trader half of the best-response system that the proof of Proposition 1 solves.
--
--   **Formalization Note** The maximizer is global and unique (the objective is a strictly concave quadratic because $1-\tau_c>0$ and $\lambda>0$).
--
--   Differences from the source:
--   - generalization: the condition at the equilibrium pricing rule $(\alpha^*,\lambda^*)$ → any intercept $\alpha$, any slope $\lambda>0$ and arbitrary linear strategies of the others; reason: under the standing assumptions with $\tau_o>0$, $\lambda^*>0$, so the source's statement is the special case $(\alpha,\lambda)=(\alpha^*,\lambda^*)$
--   - reading: "chooses $x_j$ to maximize … The first-order conditions … are $x_j=\dots$" → $x$ is a global maximizer if and only if it equals the displayed value; reason: the first-order condition of a strictly concave quadratic characterizes its unique maximizer
--   - encoding: the expectation given the trader's information $v$ → an integral over the product law of $(u,\psi)$ with $v$ fixed; reason: $v$ is independent of $(u,\psi)$, so the two coincide
--   - encoding: σv, σu, σψ, the standard deviations of the normal laws of §2, with no printed sign → σv > 0, σu > 0, σψ ≥ 0 (in the standing assumptions); reason: standard deviations are nonnegative; ṽ and ũ are genuine noise (λ* divides by σu, and with σv = 0 the interior condition fails); σψ = 0 is the degenerate case the paper itself uses in §3.4
-- source:
--   Arya–Mittendorf–Ramanan, Tax-favored Stock Donations by Corporate Insiders and Consequences for Equity Markets, SSRN 4003698 (preprint, July 2022), Appendix, proof of Proposition 1, p.A1 (PDF p.23), first-order condition of (i)

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

namespace InsiderDonations

/-- Trader `j`'s first-order condition. Arya–Mittendorf–Ramanan, SSRN 4003698 (preprint),
Appendix, proof of Proposition 1, p.A1: given the pricing rule `α − λy` with `λ > 0` and the
others' linear strategies, trader `j`'s expected utility at firm value `v` is maximized exactly at
`x = (α − v)/(2λ) − ω Σ_i E[d̂_i]/2 − Σ_{k≠j} x̂_k/2`.

**Formalization Note.** Stated for an arbitrary intercept `α`, slope `λ > 0` and arbitrary linear
strategies of the others (the page states it at `(α*, λ*)`). `E[d̂_i]` is `expDonation`, the
donation averaged over the donor's motive. "Maximizes" is read as: `x` is a global maximizer, and
the maximizer is unique. -/
theorem trader_foc {m n : ℕ} (P : Params m n) (hP : P.Standing) (s : Profile m n)
    (hlam : 0 < s.lam) (j : Fin n) (v x : ℝ) :
    (∀ x', traderPayoff P s j v x' ≤ traderPayoff P s j v x) ↔
      x = (s.α - v) / (2 * s.lam) - P.omega * (∑ i, expDonation P s i v) / 2 -
        (∑ k ∈ Finset.univ.erase j, trade s k v) / 2 := by sorry

end InsiderDonations
