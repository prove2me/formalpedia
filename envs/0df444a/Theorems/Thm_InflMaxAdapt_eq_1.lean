-- Prove2me | Theorems.Thm_InflMaxAdapt_eq_1
-- name    : InflMaxAdapt.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:39:41.344643+00:00
-- url     : https://prove2.me/theorems/a4fa2460-e488-4b1b-a222-6c88a7f08de9
-- title:
--   Eq. (1) — $\mathbb P(v \text{ activates } u) \le x_v\mathbb P(u \leftrightarrow v)$ and the resulting bound on the excess $e(v)$
-- statement:
--   Let $\pi$ be an adaptive policy (any budget, any external randomness) in the undirected-edge representation with edge probabilities $q \in [0,1]$, and let $\mathbf x$ be its seed probabilities. For every vertex $u$, every set $S \subseteq V$ and every vertex $v$:
--   1. $\mathbb P(v \text{ activates } u) \le x_v\, \mathbb P(u \leftrightarrow v)$;
--   2. the excess satisfies
--   $$
--   e(v) \;\le\; x_v \big(\mathbb P(u \leftrightarrow v,\ v \leftrightarrow S) - \mathbb P(u \leftrightarrow v,\ u \not\leftrightarrow S)\big)_+ .
--   $$
--   The first inequality is the adaptive step: when $v$ is probed, the edges between still inactive vertices follow their original law, so a policy cannot raise the chance that $v$ reaches $u$ above $\mathbb P(u \leftrightarrow v)$.
--
--   Differences from the source:
--   - encoding: adaptive policies as random sequences; probabilities over the live edges and the external randomness → policies with measurable decision rules on a probability space (Ω : Type, μ); probabilities as a finite weighted sum over live edge sets integrated against μ; reason: Lean representation of a random sequence; same policies
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Eq. (1), printed p.7 (PDF p.8), with the sentence ending on printed p.6

import Mathlib
import Definitions.Def_InflMaxAdapt_Policy_IsMeasurable
import Definitions.Def_InflMaxAdapt_activProb
import Definitions.Def_InflMaxAdapt_seedProb
import Definitions.Def_InflMaxAdapt_excess

open MeasureTheory

namespace InflMaxAdapt

/-- Eq. (1) (printed p.7 = PDF p.8, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)), with the adaptive step that precedes it: for an
adaptive policy `π` with seed probabilities `x`, every vertex `u`, set `S` and vertex `v`,
`P(v activates u) ≤ x_v P(u ↔ v)` and `e(v) ≤ x_v (P(u ↔ v, v ↔ S) − P(u ↔ v, u ↮ S))_+`. -/
theorem eq_1 {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ}
    (π : Policy V k Ω) (hπ : π.IsMeasurable) (u : V) (S : Finset V) (v : V) :
    activProb q μ π v u ≤ seedProb q μ π v * edgeProb q (fun E => Conn E u v) ∧
    excess q μ π u S v ≤ seedProb q μ π v *
      max (edgeProb q (fun E => Conn E u v ∧ ConnSet E v S) -
        edgeProb q (fun E => Conn E u v ∧ ¬ ConnSet E u S)) 0 := by sorry

end InflMaxAdapt
