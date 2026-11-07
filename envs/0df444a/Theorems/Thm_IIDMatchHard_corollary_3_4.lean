-- Prove2me | Theorems.Thm_IIDMatchHard_corollary_3_4
-- name    : IIDMatchHard.corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:18.354217+00:00
-- url     : https://prove2.me/theorems/a2bc1a3c-eb41-422d-ad18-eb6795c30d9d
-- title:
--   Corollary 3.4 — the online optimum of $I(G,\lambda)$ is close to $\widehat{\mathrm{OPT}}$
-- statement:
--   Let $G$ be a finite simple graph, $\lambda>0$ and $R=n+2m\lambda$, and let $\widehat{\mathrm{OPT}}=\sup_\pi\mathbb E[\widehat M_\pi]$ be the optimal Poisson value over all online policies of the adjusted model. Then
--   $$\widehat{\mathrm{OPT}}-\sqrt R-1\ \le\ \mathrm{OPT}(I(G,\lambda))\ \le\ \widehat{\mathrm{OPT}}+4\Delta_G\lambda^2m+\sqrt R+1.$$
--
--   The online optimum can therefore be estimated through the adjusted Poisson model, where values are easier to compute.
--
--   Differences from the source:
--   - encoding: suprema over online policies → real suprema over deterministic policies; reason: §2.1: deterministic policies attain the optimum; the Poisson values are bounded by 2n
--   - encoding: the adjusted Poisson model (a Poisson process of rate R with i.i.d. types) → the law cutLaw on (ℝ × Y)^ℕ, i.i.d. exponential gaps with independent types, K(t) the Set.ncard of {k : τ_{k+1} ≤ t}, arrivals 0-based; reason: the same process; K(t) differs only on a null event (infinitely many points, or a negative gap)
--   - encoding: E[M̂_π] → a lower Lebesgue integral of the count converted to ℝ; reason: the count is nonnegative and at most 2n; same value
--   - encoding: a deterministic policy → a function of the earlier types, the matched set and the current type; a proposal that is not a free neighbor is a rejection; reason: the matched set is a function of the earlier types for a deterministic policy; same class of policies
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Corollary 3.4, p.7 (PDF p.8); proof in App. B.3, p.16

import Definitions.Def_IIDMatchHard_Adjusted

set_option autoImplicit false

namespace IIDMatchHard

/-- **Corollary 3.4.** The online optimum of `I(G, λ)` satisfies
`ÔPT − √R − 1 ≤ OPT(I(G, λ)) ≤ ÔPT + 4∆_G λ² m + √R + 1`, where `ÔPT = sup_π E[M̂_π]` is the
optimal Poisson value over all online policies. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Corollary 3.4, p.7 (PDF p.8); proof in
App. B.3, p.16. -/
theorem corollary_3_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (lam : ℝ)
    (hlam : 0 < lam) :
    optHat G lam - Real.sqrt (totalRate G lam) - 1 ≤ OPT (cutInst G lam) ∧
      OPT (cutInst G lam) ≤ optHat G lam + 4 * (maxDeg G : ℝ) * lam ^ 2 * (numEdges G : ℝ) +
        Real.sqrt (totalRate G lam) + 1 := by sorry

end IIDMatchHard
