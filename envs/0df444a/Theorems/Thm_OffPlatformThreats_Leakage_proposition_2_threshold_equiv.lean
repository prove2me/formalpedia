-- Prove2me | Theorems.Thm_OffPlatformThreats_Leakage_proposition_2_threshold_equiv
-- name    : OffPlatformThreats.Leakage.proposition_2_threshold_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:42:29.806861+00:00
-- url     : https://prove2.me/theorems/f5f08a7f-2bf2-4299-bf91-c51b1f797974
-- title:
--   Proof of Proposition 2: the threshold of (23) as a margin condition (corrected: strict last link)
-- statement:
--   Let $c, \phi, \mu > 0$, $R_o \ge 0$, $v > 0$ and $N \ge 1$. For every real $\hat K$,
--
--   $$\left(1 - \frac{\hat K}{g_2(N, v)}\right) g_1(N, v) > R_o \iff \hat K < \frac{c\phi\mu}{N}\left(\sqrt{1 + \frac{N v}{c\phi}} - 1\right)^2 - \mu R_o\left(1 - \sqrt{\frac{c\phi}{c\phi + N v}}\right).$$
--
--   The left side says the platform earns a positive margin per transaction when it pays out $\hat K / g_2(N, v)$; the right side is the threshold condition of (23).
--
--   Differences from the source:
--
--   - correction: last link of the chain: ⟺ K̂ ≤ (cφµ/N)(√(1 + Nv/(cφ)) − 1)² − µRo(1 − √(cφ/(cφ + Nv))) → ⟺ K̂ < the same expression; reason: the previous link K̂ < g2(N, v)(1 − Ro/g1(N, v)) is strict and equals the expression; at equality the margin is 0, not positive
--   - generalization: two provider types h, l with Λ > Nµ (1), K^h ≥ K^l, and φ = (1 + c_s²)/2 → one generic type (structure Market) with arbitrary φ > 0; Λ and the two-type order conditions do not appear; reason: every object of the statement involves only the shared parameters and those of type j, and (1) is used only to justify (5); the two-type statement is the conjunction over j = h, l
--   - encoding: N^j providers of type j; a^j contains (N^j − 1)/N^j → N : ℕ with 1 ≤ N, and N − 1 computed in ℝ; reason: a^j divides by N^j; excludes only the undefined case N = 0
--   - generalization: the chain for K̂^j = max{K^j, g2(1, v^j − Ro)} → for every real K̂; reason: the chain is algebra in K̂ and holds for every value; specializes to K̂^j
--   - encoding: c (waiting cost) and µ (service rate) positive, implicit → 0 < c, 0 < µ; reason: the formulas divide by cφ and cφµ; excludes only undefined cases
--   - encoding: K̂/g2(1, v), K̂/g2(N, v) and Ro/g1(N, v), with g1, g2 defined on ℝ²₊ → 0 < v; reason: g1(n, 0) = g2(n, 0) = 0, so these quotients are undefined at v = 0; excludes only that case
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), proof of Proposition 2, Appendix p. 4 (chain after (A8))

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_g1
import Definitions.Def_OffPlatformThreats_Leakage_g2

namespace OffPlatformThreats.Leakage

/-- **The threshold of (23) as a margin condition (proof of Proposition 2), last link corrected.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), proof of Proposition 2, Appendix p. 4
(unnumbered chain after (A8)).

Let `c, φ, µ > 0`, `Ro ≥ 0`, `v > 0`, `N ≥ 1`. For every real `K̂`,
`(1 − K̂/g2(N, v)) g1(N, v) > Ro` iff
`K̂ < (cφµ/N)(√(1 + N v/(cφ)) − 1)² − µ Ro (1 − √(cφ/(cφ + N v)))`.

**Formalization Note.** The printed chain ends with `≤`; the equivalence holds with `<` (at
equality the margin `(1 − K̂/g2) g1 − Ro` is `0`). -/
theorem proposition_2_threshold_equiv (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi)
    (hmu : 0 < m.mu) (hRo : 0 ≤ m.Ro) (hv : 0 < m.v) (hN : 1 ≤ m.N) (Kh : ℝ) :
    m.Ro < (1 - Kh / g2 m m.N m.v) * g1 m m.N m.v ↔
      Kh < m.c * m.phi * m.mu / m.N * (Real.sqrt (1 + m.N * m.v / (m.c * m.phi)) - 1) ^ 2
        - m.mu * m.Ro * (1 - Real.sqrt (m.c * m.phi / (m.c * m.phi + m.N * m.v))) := by sorry

end OffPlatformThreats.Leakage
