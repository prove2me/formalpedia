-- Prove2me | Theorems.Thm_InflMaxAdapt_eq_3
-- name    : InflMaxAdapt.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:39:07.16912+00:00
-- url     : https://prove2.me/theorems/e032ad79-cf61-4505-9881-51a5e32c55b8
-- title:
--   Eq. (3) — $e(v) \le 8x_v\kappa(v)\kappa(u)$
-- statement:
--   Let $\pi$ be an adaptive policy (any budget, any external randomness) in the undirected-edge representation with edge probabilities $q \in [0,1]$, and let $\mathbf x$ be its seed probabilities. Fix a vertex $u$ and a set $S \subseteq V$, and write $\kappa(w) = \mathbb P(w \leftrightarrow S)$. Then for all $v \in V$,
--   $$
--   e(v) \;\le\; 8\, x_v\, \kappa(v)\, \kappa(u).
--   $$
--   This is the individual bound on the excess, used for seeds that rarely connect to $S$.
--
--   Differences from the source:
--   - encoding: adaptive policies as random sequences; probabilities over the live edges and the external randomness → policies with measurable decision rules on a probability space (Ω : Type, μ); probabilities as a finite weighted sum over live edge sets integrated against μ; reason: Lean representation of a random sequence; same policies
--   - encoding: live undirected edges on unordered pairs {u, v} → live edge set a Finset (Sym2 V) whose potential edges include the diagonal pairs s(v, v); reason: diagonal pairs never affect connectivity; same connection events
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Eq. (3), printed p.7 (PDF p.8)

import Mathlib
import Definitions.Def_InflMaxAdapt_Policy_IsMeasurable
import Definitions.Def_InflMaxAdapt_excess
import Definitions.Def_InflMaxAdapt_kappa
import Definitions.Def_InflMaxAdapt_seedProb

open MeasureTheory

namespace InflMaxAdapt

/-- Eq. (3) (printed p.7 = PDF p.8, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): for an adaptive policy `π` with seed probabilities
`x`, every vertex `u` and set `S`, the excess of every seed satisfies `e(v) ≤ 8 x_v κ(v) κ(u)`. -/
theorem eq_3 {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ}
    (π : Policy V k Ω) (hπ : π.IsMeasurable) (u : V) (S : Finset V) (v : V) :
    excess q μ π u S v ≤ 8 * seedProb q μ π v * kappa q S v * kappa q S u := by sorry

end InflMaxAdapt
