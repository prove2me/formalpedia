-- Prove2me | Theorems.Thm_OffPlatformThreats_Leakage_g2_strictly_increasing_in_n
-- name    : OffPlatformThreats.Leakage.g2_strictly_increasing_in_n
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:39:41.089569+00:00
-- url     : https://prove2.me/theorems/5c1a9ccd-f512-4396-98ee-7a8a48b7e92b
-- title:
--   $g_2(n, v)$ is strictly increasing in $n$
-- statement:
--   Let $c, \phi, \mu > 0$ and $v > 0$. The function $n \mapsto g_2(n, v)$ is strictly increasing on $(0, \infty)$:
--
--   $$0 < n < n' \implies g_2(n, v) < g_2(n', v).$$
--
--   By Lemma 2 this says that a provider's on-platform revenue rate increases with the number of providers on the platform (the participation externality), which is why Proposition 1 has only the outcomes $N_p = 0$ and $N_p = N$.
--
--   Differences from the source:
--
--   - generalization: ∂U_p(ω, n_p)/∂n_p > 0, i.e. g2 increasing in n, for v = v^j of the model → strict monotonicity of n ↦ g2(n, v) on n > 0 for every v > 0 and c, φ, µ > 0; reason: the claim is about the function g2 of (18); the model's v^j > 0 is an instance
--   - generalization: two provider types h, l with Λ > Nµ (1), K^h ≥ K^l, and φ = (1 + c_s²)/2 → one generic type (structure Market) with arbitrary φ > 0; Λ and the two-type order conditions do not appear; reason: every object of the statement involves only the shared parameters and those of type j, and (1) is used only to justify (5); the two-type statement is the conjunction over j = h, l
--   - encoding: c (waiting cost) and µ (service rate) positive, implicit → 0 < c, 0 < µ; reason: the formulas divide by cφ and cφµ; excludes only undefined cases
-- source:
--   He, Savin, Goh, Teo, Off-Platform Threats in On-Demand Services, SSRN 3550646 (2021-03-25 version), proof of Proposition 1, Appendix p. 2 (unnumbered); also proof of Lemma 2, Appendix p. 2

import Mathlib
import Definitions.Def_OffPlatformThreats_Leakage_Market
import Definitions.Def_OffPlatformThreats_Leakage_g2

namespace OffPlatformThreats.Leakage

/-- **`g2(n, v)` is strictly increasing in `n`.**
He, Savin, Goh & Teo, SSRN 3550646 (2021-03-25 version), proof of Proposition 1, Appendix p. 2
(unnumbered): "From (18) it follows that `∂U^j_p(ω^j, n^j_p)/∂n^j_p > 0`"; also proof of
Lemma 2, Appendix p. 2: "since `g2(n, v)` is increasing in `n`".

For `c, φ, µ > 0` and `v > 0`, `n ↦ g2(n, v)` is strictly increasing on `n > 0`. -/
theorem g2_strictly_increasing_in_n (m : Market) (hc : 0 < m.c) (hphi : 0 < m.phi)
    (hmu : 0 < m.mu) (v : ℝ) (hv : 0 < v) :
    StrictMonoOn (fun n : ℝ => g2 m n v) (Set.Ioi 0) := by sorry

end OffPlatformThreats.Leakage
