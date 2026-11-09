-- Prove2me | Theorems.Thm_InflMaxAdapt_eq_5
-- name    : InflMaxAdapt.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:39:49.31611+00:00
-- url     : https://prove2.me/theorems/768ddee5-079a-4400-a740-9658a531ea50
-- title:
--   Eq. (5) — strongly connected seeds: $\sum_{\kappa(v)\ge\beta} e(v) \le \kappa(u)/\beta$
-- statement:
--   Let $\pi$ be an adaptive policy (any budget, any external randomness) in the undirected-edge representation with edge probabilities $q \in [0,1]$, and let $\mathbf x$ be its seed probabilities. Fix a vertex $u$ and a set $S \subseteq V$, and write $\kappa(w) = \mathbb P(w \leftrightarrow S)$. Then for all $0 < \beta \le 1$,
--   $$
--   \sum_{v \in V\,:\, \kappa(v) \ge \beta} e(v) \;\le\; \frac{\kappa(u)}{\beta}.
--   $$
--   This is the collective bound on the excess of seeds that connect to $S$ with probability at least $\beta$.
--
--   Differences from the source:
--   - encoding: adaptive policies as random sequences; probabilities over the live edges and the external randomness → policies with measurable decision rules on a probability space (Ω : Type, μ); probabilities as a finite weighted sum over live edge sets integrated against μ; reason: Lean representation of a random sequence; same policies
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Eq. (5), printed p.8 (PDF p.9)

import Mathlib
import Definitions.Def_InflMaxAdapt_Policy_IsMeasurable
import Definitions.Def_InflMaxAdapt_excess
import Definitions.Def_InflMaxAdapt_kappa

open MeasureTheory

namespace InflMaxAdapt

/-- Eq. (5) (printed p.8 = PDF p.9, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)), the bound for strongly connected seeds: for an
adaptive policy `π`, every vertex `u`, set `S` and every `0 < β ≤ 1`,
`∑_{v ∈ V : κ(v) ≥ β} e(v) ≤ κ(u) / β`. -/
theorem eq_5 {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ}
    (π : Policy V k Ω) (hπ : π.IsMeasurable) (u : V) (S : Finset V) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∑ v ∈ Finset.univ.filter (fun v => β ≤ kappa q S v), excess q μ π u S v ≤ kappa q S u / β := by sorry

end InflMaxAdapt
