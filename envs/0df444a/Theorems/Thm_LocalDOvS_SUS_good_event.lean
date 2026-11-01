-- Prove2me | Theorems.Thm_LocalDOvS_SUS_good_event
-- name    : LocalDOvS.SUS.good_event
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:28:20.258907+00:00
-- url     : https://prove2.me/theorems/1b7b8da4-d5ad-46e2-affe-2cf4a77281ae
-- title:
--   Good event, pp.ec15–ec16 (corrected: one union bound over $[N] \times L$, $T_{\max} = N^2$)
-- statement:
--   Let $N\ge2$, $\sigma>0$, $\epsilon>0$, $\delta\in(0,1]$, and let $M\in\mathcal M_C$ be a model with objective $f$. With $\alpha=\delta/(2N^2)$ and $L$ the set of sample sizes of the algorithm, the good event
--
--   $$
--   G=\Big\{|\hat F_n(x)-f(x)|\le h(n,\sigma,\alpha)\ \text{ for all }x\in[N],\ n\in L\Big\}
--   $$
--
--   satisfies
--
--   $$
--   P_M(G^{c})\le\frac\delta2 .
--   $$
--
--   It is a union of at most $N(N-1)$ events, each of probability at most $\alpha$ by Hoeffding's inequality. This replaces the printed per-iteration statement that $f(x)\le f(y)$ holds with probability at least $1-\delta/T_{\max}$ for the pair $x,y$ selected by the data.
--
--   Differences from the source:
--   - correction: for the data-selected pair x, y: f(x) ≤ f(y) with probability at least 1 − δ/T_max, T_max = N, charged once per iteration → one event G over all x ∈ [N] and n ∈ L, with α = δ/(2N²) and P(Gᶜ) ≤ δ/2; reason: a pair chosen by the data does not inherit the coverage of a fixed interval, and the printed algorithm's union bound is too small; the printed theorem fails (N = 3, Gaussian noise, f = (0, 2ε, 4ε), small ε)
--   - encoding: holds with probability at least 1 − … → outer measure of the complement ≤ δ/2; reason: the same for a measurable event
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, proof of Theorem 2, pp.ec15–ec16

import Mathlib
import Definitions.Def_LocalDOvS_SUS_GoodEvent
import Definitions.Def_LocalDOvS_SUS_InMC
import Definitions.Def_LocalDOvS_SUS_tapeMeasure

open MeasureTheory
open scoped NNReal

namespace LocalDOvS.SUS

/-- **The confidence-interval event of the proof of Theorem 2, pp.ec15–ec16**
(Zhang–Zheng–Lavaei, arXiv:2012.02427v2: "By the definition of confidence intervals, we know
`f(x) ≤ f(y)` holds with probability at least `1 − δ/T_max`"), with the corrected union bound.
For every model `M ∈ M_C` on `[N]`, the good event — every interval
`[F̂_n(x) − h(n, σ, α), F̂_n(x) + h(n, σ, α)]` with `x ∈ [N]` and `n ∈ L` contains `f(x)` — fails
with probability at most `δ/2`. It is a union of at most `N(N − 1)` events of probability at
most `α = δ/(2N²)` each.

**Formalization Note.** `F̂_n(x)` is the mean of the first `n` tape entries of `x`; the bound is
on the outer measure of the complement. -/
theorem good_event (N : ℕ) (hN : 2 ≤ N) (σ : ℝ≥0) (hσ : 0 < σ) (ε : ℝ) (hε : 0 < ε)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (M : Model) (hM : InMC N σ M) :
    tapeMeasure M (GoodEvent N σ ε δ (meanFn M))ᶜ ≤ ENNReal.ofReal (δ / 2) := by sorry

end LocalDOvS.SUS
