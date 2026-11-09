-- Prove2me | Theorems.Thm_InflMaxAdapt_lemma_4
-- name    : InflMaxAdapt.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:37:01.748089+00:00
-- url     : https://prove2.me/theorems/1b15b1fb-8128-4ef2-bf5e-0a569b4b5bfa
-- title:
--   Lemma 4 — $\mathbb P(u \leftrightarrow S(\pi)) \le 2\sum_v x_v\mathbb P(u \leftrightarrow v, u \not\leftrightarrow S) + 4\sqrt{\sum_v x_v}\,\mathbb P(u \leftrightarrow S)$
-- statement:
--   Let $(V, \mathbf p)$ be an undirected instance, in the undirected-edge representation with edge probabilities $q \in [0,1]$, and let $\pi$ be an adaptive policy with seed probabilities $\mathbf x$. Then for every vertex $u \in V$ and every set $S \subseteq V$,
--   $$
--   \mathbb P\big(u \leftrightarrow S(\pi)\big) \;\le\; 2 \sum_{v \in V} x_v\, \mathbb P(u \leftrightarrow v,\ u \not\leftrightarrow S) \;+\; 4 \sqrt{\textstyle\sum_{v \in V} x_v}\; \mathbb P(u \leftrightarrow S).
--   $$
--   The square root covers $\sum_v x_v$ only. Summed over $u$, this compares any adaptive policy with a fixed seed set $S$ and gives Theorem 1.
--
--   Differences from the source:
--   - encoding: adaptive policies as random sequences; probabilities over the live edges and the external randomness → policies with measurable decision rules on a probability space (Ω : Type, μ); probabilities as a finite weighted sum over live edge sets integrated against μ; reason: Lean representation of a random sequence; same policies
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Lemma 4, printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_InflMaxAdapt_Policy_IsMeasurable
import Definitions.Def_InflMaxAdapt_hitProb
import Definitions.Def_InflMaxAdapt_seedProb
import Definitions.Def_InflMaxAdapt_kappa

open MeasureTheory

namespace InflMaxAdapt

/-- Lemma 4 (printed p.6 = PDF p.7, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): let `π` be an adaptive policy on an undirected
instance with seed probabilities `x`. Then for every vertex `u` and every set `S ⊆ V`,
`P(u ↔ S(π)) ≤ 2 ∑_v x_v P(u ↔ v, u ↮ S) + 4 √(∑_v x_v) · P(u ↔ S)`
(the square root covers `∑_v x_v` only). -/
theorem lemma_4 {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ}
    (π : Policy V k Ω) (hπ : π.IsMeasurable) (u : V) (S : Finset V) :
    hitProb q μ π u ≤
      2 * ∑ v, seedProb q μ π v * edgeProb q (fun E => Conn E u v ∧ ¬ ConnSet E u S) +
        4 * Real.sqrt (∑ v, seedProb q μ π v) * kappa q S u := by sorry

end InflMaxAdapt
