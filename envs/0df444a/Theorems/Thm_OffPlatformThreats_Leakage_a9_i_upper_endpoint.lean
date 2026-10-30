-- Prove2me | Theorems.Thm_OffPlatformThreats_Leakage_a9_i_upper_endpoint
-- name    : OffPlatformThreats.Leakage.a9_i_upper_endpoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:42:59.860579+00:00
-- url     : https://prove2.me/theorems/96972d36-3578-47ab-9dea-7417901527ce
-- title:
--   (A9)(i): positive off-platform utility iff $R_o < b$
-- statement:
--   Let $c, \phi, \mu > 0$, $K \ge 0$ and $0 \le R_o \le v$. Then
--
--   $$g_2(1, v - R_o) > K \iff R_o < b, \qquad g_2(1, v - R_o) = K \iff R_o = b .$$
--
--   By Lemma 2 the first equivalence says the off-platform utility $U_o$ is positive exactly below the upper end-point $b$; the second locates the tie $U_o = 0$ at $R_o = b$.
--
--   Differences from the source:
--
--   - generalization: (i) g2(1, v − Ro) > K ⟺ Ro < b → adds the clause g2(1, v − Ro) = K ⟺ Ro = b; reason: the tie at the end-point is what decides Proposition 3 at Ro = b; the source's equivalence is the first clause
--   - generalization: two provider types h, l with Λ > Nµ (1), K^h ≥ K^l, and φ = (1 + c_s²)/2 → one generic type (structure Market) with arbitrary φ > 0; Λ and the two-type order conditions do not appear; reason: every object of the statement involves only the shared parameters and those of type j, and (1) is used only to justify (5); the two-type statement is the conjunction over j = h, l
--   - reading: the signs of v^j and K^j are not stated → 0 ≤ v and 0 ≤ K; reason: g1, g2 are defined on ℝ²₊ (p. 15), K^j is an opportunity cost per unit time, and b^j contains √(K^j/(cφµ)), which is real only for K^j ≥ 0
--   - encoding: c (waiting cost) and µ (service rate) positive, implicit → 0 < c, 0 < µ; reason: the formulas divide by cφ and cφµ; excludes only undefined cases
--   - encoding: g2(1, v^j − Ro), with g2 defined on ℝ²₊ → Ro ≤ v; reason: excludes only arguments outside the domain of g2
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), proof of Proposition 3, (A9)(i), Appendix p. 4

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_g2
import Definitions.Def_OffPlatformThreats_Leakage_bLeak

namespace OffPlatformThreats.Leakage

/-- **(A9)(i): positive off-platform utility iff `Ro < b^j`, with the tie at `b^j`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), proof of Proposition 3, (A9)(i),
Appendix p. 4.

Let `c, φ, µ > 0`, `K ≥ 0` and `0 ≤ Ro ≤ v`. Then `g2(1, v − Ro) > K` iff `Ro < b`, and
`g2(1, v − Ro) = K` iff `Ro = b`. -/
theorem a9_i_upper_endpoint (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi) (hmu : 0 < m.mu)
    (hK : 0 ≤ m.K) (hRo : 0 ≤ m.Ro) (hRov : m.Ro ≤ m.v) :
    (m.K < g2 m 1 (m.v - m.Ro) ↔ m.Ro < bLeak m) ∧
    (g2 m 1 (m.v - m.Ro) = m.K ↔ m.Ro = bLeak m) := by sorry

end OffPlatformThreats.Leakage
