-- Prove2me | Theorems.Thm_OffPlatformThreats_Leakage_a9_ii_lower_endpoint
-- name    : OffPlatformThreats.Leakage.a9_ii_lower_endpoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:43:30.000638+00:00
-- url     : https://prove2.me/theorems/9b96636a-f84f-41cd-a32f-fff93c1ec60b
-- title:
--   (A9)(ii): the platform fails with the providers iff $R_o > a$
-- statement:
--   Let $c, \phi, \mu > 0$, $v > 0$, $N \ge 1$ and $0 \le R_o \le v$, and put $\omega = g_2(1, v - R_o)/g_2(N, v)$ (the value of $\omega^*$ in the proof of Proposition 3). Then
--
--   $$(1 - \omega)\, g_1(N, v) < R_o \iff R_o > a .$$
--
--   The left side says that, at the payout ratio needed to keep the providers on the platform, the platform's margin per transaction is below the counterparty risk it absorbs; the lower end-point $a$ of the leakage interval is where this switches.
--
--   Differences from the source:
--
--   - generalization: two provider types h, l with Λ > Nµ (1), K^h ≥ K^l, and φ = (1 + c_s²)/2 → one generic type (structure Market) with arbitrary φ > 0; Λ and the two-type order conditions do not appear; reason: every object of the statement involves only the shared parameters and those of type j, and (1) is used only to justify (5); the two-type statement is the conjunction over j = h, l
--   - encoding: N^j providers of type j; a^j contains (N^j − 1)/N^j → N : ℕ with 1 ≤ N, and N − 1 computed in ℝ; reason: a^j divides by N^j; excludes only the undefined case N = 0
--   - generalization: ω^{j*} = K̂^j/g2(N^j, v^j) = g2(1, v^j − Ro)/g2(N^j, v^j), valid since g2(1, v^j − Ro) > K^j → ω := g2(1, v − Ro)/g2(N, v), with no condition relating g2(1, v − Ro) and K; reason: the equivalence is about g1, g2 alone; specializes to the source's case g2(1, v − Ro) > K
--   - encoding: c (waiting cost) and µ (service rate) positive, implicit → 0 < c, 0 < µ; reason: the formulas divide by cφ and cφµ; excludes only undefined cases
--   - encoding: K̂/g2(1, v), K̂/g2(N, v) and Ro/g1(N, v), with g1, g2 defined on ℝ²₊ → 0 < v; reason: g1(n, 0) = g2(n, 0) = 0, so these quotients are undefined at v = 0; excludes only that case
--   - encoding: g2(1, v^j − Ro), with g2 defined on ℝ²₊ → Ro ≤ v; reason: excludes only arguments outside the domain of g2
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), proof of Proposition 3, (A9)(ii), Appendix pp. 4–5

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_g1
import Definitions.Def_OffPlatformThreats_Leakage_g2
import Definitions.Def_OffPlatformThreats_Leakage_aLeak

namespace OffPlatformThreats.Leakage

/-- **(A9)(ii): the platform fails with the providers iff `Ro > a^j`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), proof of Proposition 3, (A9)(ii),
Appendix pp. 4–5.

Let `c, φ, µ > 0`, `v > 0`, `N ≥ 1` and `0 ≤ Ro ≤ v`, and let
`ω = g2(1, v − Ro)/g2(N, v)` (the value of `ω^{j*}` used in (A9)). Then
`(1 − ω) g1(N, v) < Ro` iff `Ro > a`. -/
theorem a9_ii_lower_endpoint (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (hv : 0 < m.v) (hN : 1 ≤ m.N) (hRo : 0 ≤ m.Ro) (hRov : m.Ro ≤ m.v) :
    (1 - g2 m 1 (m.v - m.Ro) / g2 m m.N m.v) * g1 m m.N m.v < m.Ro ↔ aLeak m < m.Ro := by sorry

end OffPlatformThreats.Leakage
