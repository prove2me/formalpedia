-- Prove2me | Theorems.Thm_IIDMatchHard_lemma_3_6
-- name    : IIDMatchHard.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:30.865229+00:00
-- url     : https://prove2.me/theorems/7823207f-2e9c-4a95-bf4d-4e465427fbf3
-- title:
--   Lemma 3.6 — the Poisson value of a cut policy
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices, $m$ edges and largest degree $\Delta_G$, and let $\lambda>0$. For each cut $\sigma$ of $G$ and its induced online matching policy $\pi_\sigma$, run in the adjusted Poisson model of $I(G,\lambda)$,
--   $$\Phi_G(|\delta_G(\sigma)|)-4\Delta_G\lambda^2m\ \le\ \mathbb E[\widehat M_{\pi_\sigma}]\ \le\ \Phi_G(|\delta_G(\sigma)|),$$
--   where $\Phi_G$ is the affine function
--   $$\Phi_G(x)=\Big(2-\frac3e\Big)n+\Big(\frac1e+\frac9{e^2}\Big)\lambda m+\Big(\frac2e-\frac5{e^2}\Big)\lambda x.$$
--
--   Larger cuts give cut policies with larger Poisson value, and the slope $(2/e-5/e^2)\lambda$ is positive.
--
--   Differences from the source:
--   - generalization: π_σ with ties broken by a fixed order of V → π_σ for every linear order o of V; reason: the paper order is one such order
--   - encoding: the adjusted Poisson model (a Poisson process of rate R with i.i.d. types) → the law cutLaw on (ℝ × Y)^ℕ, i.i.d. exponential gaps with independent types, K(t) the Set.ncard of {k : τ_{k+1} ≤ t}, arrivals 0-based; reason: the same process; K(t) differs only on a null event (infinitely many points, or a negative gap)
--   - encoding: E[M̂_π] → a lower Lebesgue integral of the count converted to ℝ; reason: the count is nonnegative and at most 2n; same value
--   - encoding: e in Φ → Real.exp 1; reason: Lean convention; same quantity
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Lemma 3.6, p.9 (PDF p.10); proof in App. B.6, p.20

import Definitions.Def_IIDMatchHard_Adjusted

set_option autoImplicit false

namespace IIDMatchHard

/-- **Lemma 3.6 (The value of a cut policy).** For each cut `σ` of `G` and its induced online
matching policy `π_σ`, `Φ_G(|δ_G(σ)|) − 4∆_G λ² m ≤ E[M̂_{π_σ}] ≤ Φ_G(|δ_G(σ)|)`, where
`Φ_G(x) = (2 − 3/e)n + (1/e + 9/e²)λm + (2/e − 5/e²)λx`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Lemma 3.6, p.9 (PDF p.10);
proof in App. B.6, p.20.

**Formalization Note.** `π_σ` (Algorithm 1) breaks ties by a fixed order of `V`; the statement
holds for every such order `o`. It is run in the adjusted model (App. B.5, p.18). -/
theorem lemma_3_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (lam : ℝ)
    (hlam : 0 < lam) (o : LinearOrder V) (σ : V → Bool) :
    Phi G lam (cutSize G σ) - 4 * (maxDeg G : ℝ) * lam ^ 2 * (numEdges G : ℝ) ≤
        poissonValue G lam (cutPolicy G o σ) ∧
      poissonValue G lam (cutPolicy G o σ) ≤ Phi G lam (cutSize G σ) := by sorry

end IIDMatchHard
