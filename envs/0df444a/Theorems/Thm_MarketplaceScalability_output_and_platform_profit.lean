-- Prove2me | Theorems.Thm_MarketplaceScalability_output_and_platform_profit
-- name    : MarketplaceScalability.output_and_platform_profit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:17.898992+00:00
-- url     : https://prove2.me/theorems/59de6869-938a-4dea-b5d8-ce02c8c0b8ce
-- title:
--   §3.1 — $q_o>q_m$ and $\pi_o\ge\pi_m$ (corrected: demand conditions)
-- statement:
--   The map $q$ is strictly decreasing on $(0,\bar c]$; hence
--   $$
--   q_m<q_o,\qquad \pi_m\le\pi_o,
--   $$
--   and $\pi_m<\pi_o$ when $\alpha>0$.
--
--   So the platform earns at least as much when sellers can scale, if it does not offer the service.
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - reading: πo > πm (p.9) → π_m ≤ π_o, strict when α > 0; reason: at α = 0 both profits vanish; the source's α ∈ (0, 1) gets the strict inequality, and the proof of Proposition 1 uses the weak form
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §3.1, p.9

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_piM
import Definitions.Def_MarketplaceScalability_Params_piO

namespace MarketplaceScalability

/-- **§3.1, p.9.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: "Note that qo = q(c̲) > q(c̄) = qm, and thus πo > πm."

`q` is strictly decreasing on `(0, c̄]`, so `q_m < q_o`; `π_m ≤ π_o`, strictly when `α > 0`.

**Formalization Note** The model admits `α = 0`, where `π_m = π_o = 0`; the proof of Proposition 1
(p.26) uses the weak form `π_o ≥ π_m`. -/
theorem output_and_platform_profit (M : Model) :
    StrictAntiOn M.q (Set.Ioc 0 M.cbar) ∧
    M.qm < M.qo ∧
    M.piM ≤ M.piO ∧
    (0 < M.α → M.piM < M.piO) := by sorry

end MarketplaceScalability
