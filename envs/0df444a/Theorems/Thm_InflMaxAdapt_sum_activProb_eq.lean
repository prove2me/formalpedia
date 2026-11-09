-- Prove2me | Theorems.Thm_InflMaxAdapt_sum_activProb_eq
-- name    : InflMaxAdapt.sum_activProb_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:39:19.773815+00:00
-- url     : https://prove2.me/theorems/59bfacd6-2967-4e37-835a-02d0ffd74442
-- title:
--   Proof of Lemma 4 — the contributions of the seeds sum to $\mathbb P(u \leftrightarrow S(\pi))$
-- statement:
--   Let $\pi$ be an adaptive policy (any budget, any external randomness) in the undirected-edge representation with edge probabilities $q \in [0,1]$, and let $\mathbf x$ be its seed probabilities. For every vertex $u$,
--   $$
--   \sum_{v \in V} \mathbb P(v \text{ activates } u) \;=\; \mathbb P\big(u \leftrightarrow S(\pi)\big),
--   $$
--   where $v$ activates $u$ if $v$ is probed by $\pi$, $u$ is connected to $v$, and $u$ is not connected to the seeds probed before $v$.
--
--   The identity splits the activation probability of $u$ into the contributions of the individual seeds, which the rest of the proof of Lemma 4 bounds.
--
--   Differences from the source:
--   - encoding: adaptive policies as random sequences; probabilities over the live edges and the external randomness → policies with measurable decision rules on a probability space (Ω : Type, μ); probabilities as a finite weighted sum over live edge sets integrated against μ; reason: Lean representation of a random sequence; same policies
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), proof of Lemma 4, printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_InflMaxAdapt_Policy_IsMeasurable
import Definitions.Def_InflMaxAdapt_activProb
import Definitions.Def_InflMaxAdapt_hitProb

open MeasureTheory

namespace InflMaxAdapt

/-- The contributions sum to the activation probability (proof of Lemma 4, printed p.6 = PDF p.7,
of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): for an adaptive policy `π` in the undirected-edge representation and every vertex `u`,
`∑_{v ∈ V} P(v activates u) = P(u ↔ S(π))`. -/
theorem sum_activProb_eq {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ}
    (π : Policy V k Ω) (hπ : π.IsMeasurable) (u : V) :
    ∑ v, activProb q μ π v u = hitProb q μ π u := by sorry

end InflMaxAdapt
