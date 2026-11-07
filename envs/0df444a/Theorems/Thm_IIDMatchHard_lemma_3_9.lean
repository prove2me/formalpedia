-- Prove2me | Theorems.Thm_IIDMatchHard_lemma_3_9
-- name    : IIDMatchHard.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:07:23.15176+00:00
-- url     : https://prove2.me/theorems/1067e24f-0a39-4804-9997-dedf12faf4ab
-- title:
--   Lemma 3.9 — the adaptivity gap
-- statement:
--   Let $G$ be a finite simple graph with $m$ edges and largest degree $\Delta_G$, let $B\ge1$, let $\tilde G$ be the blow-up of $G$ and let $\lambda>0$. Let $\sigma$ be a maximum cut of $\tilde G$. On the instance $I(\tilde G,\lambda)$,
--   $$\mathbb E[\widehat M_{\pi_\sigma}]\ \le\ \widehat{\mathrm{OPT}}\ \le\ \mathbb E[\widehat M_{\pi_\sigma}]+\lambda mB^{3/2}+4\Delta_G\lambda^2mB^3.$$
--
--   On a blow-up, the policy of a maximum cut is nearly optimal in the adjusted Poisson model: no adaptive policy gains more than $O(\lambda mB^{3/2}+\Delta_G\lambda^2mB^3)$ over it.
--
--   Differences from the source:
--   - generalization: π_σ with ties broken by a fixed order of V × {1, …, B} → π_σ for every linear order o of V × Fin B; reason: the paper order is one such order
--   - encoding: the adjusted Poisson model (a Poisson process of rate R with i.i.d. types) → the law cutLaw on (ℝ × Y)^ℕ, i.i.d. exponential gaps with independent types, K(t) the Set.ncard of {k : τ_{k+1} ≤ t}, arrivals 0-based; reason: the same process; K(t) differs only on a null event (infinitely many points, or a negative gap)
--   - encoding: E[M̂_π] → a lower Lebesgue integral of the count converted to ℝ; reason: the count is nonnegative and at most 2n; same value
--   - encoding: suprema over online policies → real suprema over deterministic policies; reason: §2.1: deterministic policies attain the optimum; the values are bounded
--   - encoding: e in Φ → Real.exp 1; reason: Lean convention; same quantity
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Lemma 3.9, p.10 (PDF p.11); proof in App. B.8, pp.21–22

import Definitions.Def_IIDMatchHard_Adjusted

set_option autoImplicit false

namespace IIDMatchHard

/-- **Lemma 3.9 (Adaptivity gap).** Let `σ` be a maximum cut of `G̃`. On the instance
`I(G̃, λ)`, `E[M̂_{π_σ}] ≤ ÔPT ≤ E[M̂_{π_σ}] + λmB^{3/2} + 4∆_G λ² m B³`. Teng, Yang, *Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026,
sha256 f0193d92…), Lemma 3.9,
p.10 (PDF p.11); proof in App. B.8, pp.21–22.

**Formalization Note.** `G̃ = blowUp G B` with `B ≥ 1`; `m` and `∆_G` are those of `G`. The
policy `π_σ` breaks ties by any fixed order `o` of the vertices of `G̃`. -/
theorem lemma_3_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (B : ℕ)
    (hB : 1 ≤ B) (lam : ℝ) (hlam : 0 < lam) (o : LinearOrder (V × Fin B))
    (σ : V × Fin B → Bool) (hσ : cutSize (blowUp G B) σ = maxCut (blowUp G B)) :
    poissonValue (blowUp G B) lam (cutPolicy (blowUp G B) o σ) ≤ optHat (blowUp G B) lam ∧
      optHat (blowUp G B) lam ≤ poissonValue (blowUp G B) lam (cutPolicy (blowUp G B) o σ) +
        lam * (numEdges G : ℝ) * (B : ℝ) ^ (3 / 2 : ℝ) +
        4 * (maxDeg G : ℝ) * lam ^ 2 * (numEdges G : ℝ) * (B : ℝ) ^ 3 := by sorry

end IIDMatchHard
