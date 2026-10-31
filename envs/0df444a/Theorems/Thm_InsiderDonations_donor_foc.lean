-- Prove2me | Theorems.Thm_InsiderDonations_donor_foc
-- name    : InsiderDonations.donor_foc
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:46.217985+00:00
-- url     : https://prove2.me/theorems/c18e24e0-bd3b-4573-999d-73c2cd89dd0d
-- title:
--   Appendix, proof of Proposition 1, p.A1 — donor $i$'s first-order condition
-- statement:
--   Fix a linear profile with pricing rule $P(y)=\alpha-\lambda y$, $\lambda>0$, under the standing assumptions and $\tau_o>0$. For donor $i$, firm value $v$, own motive $\psi_i$, and the other agents' linear strategies (written $\hat d_k$, $\hat x_j$), donor $i$ chooses $d$ to maximize
--   $$
--   E\Big[(H_i-d)(1-\tau_c)v+I_i-\Big(I_i-\Big(\alpha-\lambda\Big(u+\omega d+\omega\sum_{k\ne i}\hat d_k+\sum_{j=1}^n\hat x_j\Big)\Big)d\Big)\tau_o+\psi_i d\Big],
--   $$
--   the expectation being over $u$ and the other donors' motives. Then $d$ maximizes this expected utility if and only if
--   $$
--   d=\frac{\alpha-v[1-\tau_c]/\tau_o}{2\lambda\omega}-\frac{\sum_{k\ne i}E[\hat d_k]}{2}-\frac{\sum_{j=1}^n\hat x_j}{2\omega}+\frac{\psi_i}{2\lambda\omega\tau_o}.
--   $$
--
--   This is the donor half of the best-response system that the proof of Proposition 1 solves.
--
--   **Formalization Note** $E[\hat d_k]$ is donor $k$'s donation at $v$ averaged over her motive. The integrand is the utility $U_i$ of p.4, which equals the appendix's form $(H_i-d)(1-\tau_c)v+\tau_oPd+\psi_id+I_i(1-\tau_o)$.
--
--   Differences from the source:
--   - generalization: the condition at the equilibrium pricing rule $(\alpha^*,\lambda^*)$ → any intercept $\alpha$, any slope $\lambda>0$ and arbitrary linear strategies of the others; reason: under the standing assumptions with $\tau_o>0$, $\lambda^*>0$, so the source's statement is the special case $(\alpha,\lambda)=(\alpha^*,\lambda^*)$
--   - reading: tax rates (printed assumption $\tau_c\le\tau_o<1/2$ only) → hypothesis $0<\tau_o$; reason: tax rates are nonnegative; with $\tau_o<0$ the printed assumptions admit instances with no equilibrium (e.g. $m=1$, $n=10$, $\tau_o=-1$, $\tau_c=-2$, $\sigma_\psi=0$)
--   - reading: "chooses $d_i$ to maximize … The first-order conditions … are $d_i=\dots$" → $d$ is a global maximizer if and only if it equals the displayed value; reason: the first-order condition of a strictly concave quadratic characterizes its unique maximizer
--   - encoding: the expectation given the donor's information $(v,\psi_i)$ → an integral over the product law of $(u,\psi)$ with $v$ and the donor's own motive fixed, her own noise coordinate unread; reason: $v$, $u$ and the motives are independent, so the two coincide
--   - encoding: σv, σu, σψ, the standard deviations of the normal laws of §2, with no printed sign → σv > 0, σu > 0, σψ ≥ 0 (in the standing assumptions); reason: standard deviations are nonnegative; ṽ and ũ are genuine noise (λ* divides by σu, and with σv = 0 the interior condition fails); σψ = 0 is the degenerate case the paper itself uses in §3.4
-- source:
--   Arya–Mittendorf–Ramanan, Tax-favored Stock Donations by Corporate Insiders and Consequences for Equity Markets, SSRN 4003698 (preprint, July 2022), Appendix, proof of Proposition 1, p.A1 (PDF p.23), first-order condition of (ii); utility U_i, §2, p.4

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

namespace InsiderDonations

/-- Donor `i`'s first-order condition. Arya–Mittendorf–Ramanan, SSRN 4003698 (preprint),
Appendix, proof of Proposition 1, p.A1: given the pricing rule `α − λy` with `λ > 0` and the
others' linear strategies, donor `i`'s expected utility at firm value `v` and own motive `ψ₀` is
maximized exactly at
`d = (α − v[1 − τc]/τo)/(2λω) − Σ_{k≠i} E[d̂_k]/2 − Σ_j x̂_j/(2ω) + ψ₀/(2λωτo)`.

**Formalization Note.** Stated for an arbitrary intercept `α`, slope `λ > 0` and arbitrary linear
strategies of the others (the page states it at `(α*, λ*)`). `0 < τo` is the reading "tax rates
are nonnegative". -/
theorem donor_foc {m n : ℕ} (P : Params m n) (hP : P.Standing) (hτo : 0 < P.τo)
    (s : Profile m n) (hlam : 0 < s.lam) (i : Fin m) (v ψ₀ d : ℝ) :
    (∀ d', donorPayoff P s i v ψ₀ d' ≤ donorPayoff P s i v ψ₀ d) ↔
      d = (s.α - v * (1 - P.τc) / P.τo) / (2 * s.lam * P.omega) -
        (∑ k ∈ Finset.univ.erase i, expDonation P s k v) / 2 -
        (∑ j, trade s j v) / (2 * P.omega) + ψ₀ / (2 * s.lam * P.omega * P.τo) := by sorry

end InsiderDonations
