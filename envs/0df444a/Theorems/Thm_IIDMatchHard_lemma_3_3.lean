-- Prove2me | Theorems.Thm_IIDMatchHard_lemma_3_3
-- name    : IIDMatchHard.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:19.245971+00:00
-- url     : https://prove2.me/theorems/61537d03-de8d-4fd3-a8e4-1682c6153d00
-- title:
--   Lemma 3.3 — the adjusted Poisson model approximates the i.i.d. value
-- statement:
--   Let $G$ be a finite simple graph, $\lambda>0$ and $R=n+2m\lambda$. For every deterministic policy $\pi$ for $I(G,\lambda)$,
--   $$\mathbb E[M_\pi(T)]-4\Delta_G\lambda^2m-\sqrt R-1\ \le\ \mathbb E[\widehat M_\pi]\ \le\ \mathbb E[M_\pi(T)]+\sqrt R+1,$$
--   where $\mathbb E[M_\pi(T)]$ is the value of $\pi$ on $I(G,\lambda)$ with $T=\lceil R\rceil$ i.i.d. arrivals. $\widehat M_\pi$ is the number of matches when $\pi$ runs in the adjusted Poisson model, taking the same decisions as in $I(G,\lambda)$ except that it rejects every blocked arrival.
--
--   The values of a policy under i.i.d. and adjusted Poisson arrivals differ by $O(\sqrt R+\Delta_G\lambda^2m)$.
--
--   Differences from the source:
--   - reading: π, a policy for I(G, λ), run in the adjusted model → the transferred policy transfer G π: it rejects blocked arrivals and otherwise takes the decision π takes in I(G, λ); reason: App. B.3, p.16: "In the adjusted model, π takes the same decisions as in I(G, λ), except that it rejects every blocked arrival"
--   - encoding: E[M̂_π] → a lower Lebesgue integral of the count converted to ℝ; reason: the count is nonnegative and at most 2n; same value
--   - encoding: the adjusted Poisson model (a Poisson process of rate R with i.i.d. types) → the law cutLaw on (ℝ × Y)^ℕ, i.i.d. exponential gaps with independent types, K(t) the Set.ncard of {k : τ_{k+1} ≤ t}, arrivals 0-based; reason: the same process; K(t) differs only on a null event (infinitely many points, or a negative gap)
--   - encoding: a deterministic policy → a function of the earlier types, the matched set and the current type; a proposal that is not a free neighbor is a rejection; reason: the matched set is a function of the earlier types for a deterministic policy; same class of policies
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Lemma 3.3, p.7 (PDF p.8); proof in App. B.3, p.16

import Definitions.Def_IIDMatchHard_Adjusted

set_option autoImplicit false

namespace IIDMatchHard

/-- **Lemma 3.3 (The adjusted Poisson model).** For every deterministic policy `π` for
`I(G, λ)`, `E[M_π(T)] − 4∆_G λ² m − √R − 1 ≤ E[M̂_π] ≤ E[M_π(T)] + √R + 1`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Lemma 3.3,
p.7 (PDF p.8); proof in App. B.3, p.16.

**Formalization Note.** `E[M_π(T)]` is the i.i.d. value of `π` on `I(G, λ)` with `T = ⌈R⌉`. In the
adjusted model `π` "takes the same decisions as in I(G, λ), except that it rejects every blocked
arrival" (p.16): `M̂_π` is the run of `transfer G π`. -/
theorem lemma_3_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (lam : ℝ)
    (hlam : 0 < lam) (π : Policy (V × Bool) (IType G)) :
    value (cutInst G lam) π - 4 * (maxDeg G : ℝ) * lam ^ 2 * (numEdges G : ℝ) -
          Real.sqrt (totalRate G lam) - 1 ≤ poissonValue G lam (transfer G π) ∧
      poissonValue G lam (transfer G π) ≤
        value (cutInst G lam) π + Real.sqrt (totalRate G lam) + 1 := by sorry

end IIDMatchHard
