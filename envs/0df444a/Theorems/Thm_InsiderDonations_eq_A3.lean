-- Prove2me | Theorems.Thm_InsiderDonations_eq_A3
-- name    : InsiderDonations.eq_A3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:02.673735+00:00
-- url     : https://prove2.me/theorems/bbd49d97-ac29-4ce6-9c34-9c006c6d64f7
-- title:
--   (A3), p.A1 — the best responses of all traders and donors solve simultaneously
-- statement:
--   Under the standing assumptions and $\tau_o>0$, fix a linear profile whose pricing rule $P(y)=\alpha-\lambda y$ has $\lambda>0$. Then every trader and every donor best-responds (for every firm value $v$, and every motive $\psi_i$ for the donors) if and only if, for all $j$, $i$, $v$ and $\psi_i$,
--   $$
--   x_j=-\frac{m\bar\psi}{[1+m+n]\lambda\tau_o}+\frac{\alpha}{[1+m+n]\lambda}-v\left[\frac{(1+m)\tau_o-m(1-\tau_c)}{(1+m+n)\lambda\tau_o}\right]
--   $$
--   and
--   $$
--   d_i=\frac{[1+n][\psi_i+\bar\psi]+m[\psi_i-\bar\psi]}{2[1+m+n]\lambda\omega\tau_o}+\frac{\alpha}{[1+m+n]\lambda\omega}-v\left[\frac{(1+n)(1-\tau_c)-n\tau_o}{(1+m+n)\lambda\omega\tau_o}\right].
--   $$
--
--   In particular the agents' strategies are symmetric. Combined with the market maker's pricing (A4), this pins down Proposition 1.
--
--   **Formalization Note** The coefficients of the profile are a priori arbitrary and may differ across agents; the conjectures $\hat x_k,\hat d_k$ of the page are the other agents' actual strategies.
--
--   Differences from the source:
--   - generalization: the simultaneous solution at $(\alpha^*,\lambda^*)$ → any intercept $\alpha$ and slope $\lambda>0$; reason: $\lambda^*>0$ under the standing assumptions with $\tau_o>0$, so the source's (A3) is the special case $(\alpha,\lambda)=(\alpha^*,\lambda^*)$
--   - reading: tax rates (printed assumption $\tau_c\le\tau_o<1/2$ only) → hypothesis $0<\tau_o$; reason: tax rates are nonnegative; with $\tau_o<0$ the printed assumptions admit instances with no equilibrium
--   - reading: "simultaneously solving the above, alongside the fact that conjectures hold in equilibrium, yields" → an iff between joint optimality of all traders and donors and the displayed strategies; reason: this is what solving the best-response system means; the iff gives both that (A3) is optimal and that nothing else is
--   - encoding: each agent's expectation given her information ($v$ for a trader, $(v,\psi_i)$ for a donor) → an integral over the product law of $(u,\psi)$ with that information fixed, optimality required at every realization; reason: $v$, $u$ and the motives are independent, so the two coincide, and the page's first-order conditions are pointwise in $v$ and $\psi_i$
--   - encoding: σv, σu, σψ, the standard deviations of the normal laws of §2, with no printed sign → σv > 0, σu > 0, σψ ≥ 0 (in the standing assumptions); reason: standard deviations are nonnegative; ṽ and ũ are genuine noise (λ* divides by σu, and with σv = 0 the interior condition fails); σψ = 0 is the degenerate case the paper itself uses in §3.4
-- source:
--   Arya–Mittendorf–Ramanan, Tax-favored Stock Donations by Corporate Insiders and Consequences for Equity Markets, SSRN 4003698 (preprint, July 2022), Appendix, proof of Proposition 1, (A3), p.A1 (PDF p.23)

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

namespace InsiderDonations

/-- (A3). Arya–Mittendorf–Ramanan, SSRN 4003698 (preprint), Appendix, proof of Proposition 1,
(A3), p.A1: given the pricing rule `α − λy` with `λ > 0`, a linear profile has every trader and
every donor best-responding exactly when
`d_i = ([1+n][ψ_i+ψ̄] + m[ψ_i−ψ̄])/(2[1+m+n]λωτo) + α/([1+m+n]λω) − v((1+n)(1−τc) − nτo)/((1+m+n)λωτo)`
and
`x_j = −mψ̄/([1+m+n]λτo) + α/([1+m+n]λ) − v((1+m)τo − m(1−τc))/((1+m+n)λτo)`.

**Formalization Note.** Stated for an arbitrary `α` and `λ > 0` (the page states it at
`(α*, λ*)`); strategies may a priori differ across agents. -/
theorem eq_A3 {m n : ℕ} (P : Params m n) (hP : P.Standing) (hτo : 0 < P.τo)
    (s : Profile m n) (hlam : 0 < s.lam) :
    TraderOptimal P s ∧ DonorOptimal P s ↔
      (∀ j v, trade s j v =
        -(m * P.ψbar / ((1 + m + n) * s.lam * P.τo)) + s.α / ((1 + m + n) * s.lam) -
          v * (((1 + m) * P.τo - m * (1 - P.τc)) / ((1 + m + n) * s.lam * P.τo))) ∧
      (∀ i v ψ, donate s i v ψ =
        ((1 + n) * (ψ + P.ψbar) + m * (ψ - P.ψbar)) / (2 * (1 + m + n) * s.lam * P.omega * P.τo) +
          s.α / ((1 + m + n) * s.lam * P.omega) -
          v * (((1 + n) * (1 - P.τc) - n * P.τo) / ((1 + m + n) * s.lam * P.omega * P.τo))) := by sorry

end InsiderDonations
