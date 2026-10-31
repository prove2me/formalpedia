-- Prove2me | Theorems.Thm_InsiderDonations_eta_mse
-- name    : InsiderDonations.eta_mse
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:02.135584+00:00
-- url     : https://prove2.me/theorems/08b4b070-711a-4480-8e5f-e212fac882c4
-- title:
--   §3.2, p.11 — $\eta=1-E[(P^*-v)^2]/\sigma_v^2$
-- statement:
--   Under the standing assumptions and $\tau_o>0$, the price-informativeness weight $\eta=(m[1-\tau_c]+n\tau_o)/([1+m+n]\tau_o)$ of the recast price satisfies
--   $$
--   \eta=1-\frac{E[(P^*-v)^2]}{\sigma_v^2},
--   $$
--   where $P^*$ is the equilibrium price of Proposition 1 and the expectation is over $(v,u,\psi)$.
--
--   $E[(P^*-v)^2]$ measures how far the stock price is from the firm's underlying value on average; its reciprocal is the price efficiency $\Omega$ of Proposition 3.
--
--   Differences from the source:
--   - reading: tax rates (printed assumption $\tau_c\le\tau_o<1/2$ only) → hypothesis $0<\tau_o$; reason: tax rates are nonnegative; with $\tau_o<0$ the printed $\lambda^*$ can be negative and Proposition 1's profile is not an equilibrium
--   - encoding: $\tilde v$, $\tilde u$, $\tilde\psi_i$ independent normals → the product of `gaussianReal` laws on $\mathbb R\times\mathbb R\times\mathbb R^m$; reason: same joint law
--   - encoding: σv, σu, σψ, the standard deviations of the normal laws of §2, with no printed sign → σv > 0, σu > 0, σψ ≥ 0 (in the standing assumptions); reason: standard deviations are nonnegative; ṽ and ũ are genuine noise (λ* divides by σu, and with σv = 0 the interior condition fails); σψ = 0 is the degenerate case the paper itself uses in §3.4
-- source:
--   Arya–Mittendorf–Ramanan, Tax-favored Stock Donations by Corporate Insiders and Consequences for Equity Markets, SSRN 4003698 (preprint, July 2022), §3.2, p.11 (PDF p.13), first sentence

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

namespace InsiderDonations

/-- `η = 1 − E[(P* − v)²]/σv²`. Arya–Mittendorf–Ramanan, SSRN 4003698 (preprint), §3.2, p.11: from
Proposition 1, `η` can be equivalently expressed as `1 − E[(P* − v)²]/σv²`.

**Formalization Note.** `P*` is the price of the profile `eqProfile` of Proposition 1 and the
expectation is over the model's law. -/
theorem eta_mse {m n : ℕ} (P : Params m n) (hP : P.Standing) (hτo : 0 < P.τo) :
    eta P = 1 - (∫ ω, (price (eqProfile P) (orderFlow P (eqProfile P) ω) - ω.1) ^ 2 ∂(law P)) /
      P.σv ^ 2 := by sorry

end InsiderDonations
