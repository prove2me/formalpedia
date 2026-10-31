-- Prove2me | Theorems.Thm_InsiderDonations_price_recast
-- name    : InsiderDonations.price_recast
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:57.733989+00:00
-- url     : https://prove2.me/theorems/6f7dce87-64fd-41e3-89fe-10985097e615
-- title:
--   §3.2, p.9 — $P^*=\eta v+[1-\eta]\bar v-\lambda^*u-\sum_i(\psi_i-\bar\psi)/(2\tau_o)$
-- statement:
--   Under the standing assumptions and $\tau_o>0$, the equilibrium price of Proposition 1 can be recast in terms of the firm's underlying value: at every outcome $(v,u,\psi_1,\dots,\psi_m)$,
--   $$
--   P^*=\eta v+[1-\eta]\bar v-\lambda^*u-\frac{\sum_{i=1}^m(\psi_i-\bar\psi)}{2\tau_o},\qquad \eta=\frac{m[1-\tau_c]+n\tau_o}{[1+m+n]\tau_o}.
--   $$
--
--   The weight $\eta$ on $v$ measures how much private information the price embeds; it is the bridge from Proposition 1 to the price-efficiency measure of Proposition 3.
--
--   **Formalization Note** $P^*$ is the price $\alpha^*-\lambda^*y$ of Proposition 1's profile, evaluated at the order flow that profile generates; the identity holds at every outcome, not just almost surely.
--
--   Differences from the source:
--   - reading: tax rates (printed assumption $\tau_c\le\tau_o<1/2$ only) → hypothesis $0<\tau_o$; reason: tax rates are nonnegative; with $\tau_o<0$ the printed $\lambda^*$ can be negative and Proposition 1's profile is not an equilibrium
--   - encoding: σv, σu, σψ, the standard deviations of the normal laws of §2, with no printed sign → σv > 0, σu > 0, σψ ≥ 0 (in the standing assumptions); reason: standard deviations are nonnegative; ṽ and ũ are genuine noise (λ* divides by σu, and with σv = 0 the interior condition fails); σψ = 0 is the degenerate case the paper itself uses in §3.4
-- source:
--   Arya–Mittendorf–Ramanan, Tax-favored Stock Donations by Corporate Insiders and Consequences for Equity Markets, SSRN 4003698 (preprint, July 2022), §3.2, display on p.9 (PDF p.11)

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

namespace InsiderDonations

/-- The price recast. Arya–Mittendorf–Ramanan, SSRN 4003698 (preprint), §3.2, display on p.9: the
equilibrium price of Proposition 1 is
`P* = ηv + [1 − η]v̄ − λ*u − Σ_i (ψ_i − ψ̄)/(2τo)` with `η = (m[1−τc] + nτo)/([1+m+n]τo)`.

**Formalization Note.** A pointwise identity at every outcome `(v, u, ψ)`, for the profile
`eqProfile` of Proposition 1. -/
theorem price_recast {m n : ℕ} (P : Params m n) (hP : P.Standing) (hτo : 0 < P.τo)
    (ω : Outcome m) :
    price (eqProfile P) (orderFlow P (eqProfile P) ω) =
      eta P * ω.1 + (1 - eta P) * P.vbar - lamStar P * ω.2.1 -
        (∑ i, (ω.2.2 i - P.ψbar)) / (2 * P.τo) := by sorry

end InsiderDonations
