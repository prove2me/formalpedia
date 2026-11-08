-- Prove2me | Theorems.Thm_GraphonCheeger_theorem_4_33
-- name    : GraphonCheeger.theorem_4_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:01:51.630613+00:00
-- url     : https://prove2.me/theorems/04c9bf4c-57d2-460b-9a4c-9da5ffe69faa
-- title:
--   Theorem 4.33: if $G_n\to W$ and $d_{\min}(G_n)\ge c|G_n|$, then $k_W\ge c$ a.e. and $h(G_n)\to h(W)$
-- statement:
--   Let $G_n$ be finite graphs with $|G_n|\to\infty$, and suppose that $G_n\to W$ for a graphon $W$ on a probability space $(\Omega,\mathcal F,\mu)$, that is, $\delta_\square(W_{G_n},W)\to0$ for the continuous graphons $W_{G_n}$ on $[0,1]$. Assume that for some $c>0$,
--
--   $$d_{\min}(G_n)\ge c\,|G_n|$$
--
--   for all sufficiently large $n$. Then $k_W\ge c$ almost everywhere, and
--
--   $$h(G_n)\to h(W),$$
--
--   where $h(W)$ is the mixed Cheeger constant of $W$.
--
--   The Cheeger constant of a dense graph with linear minimum degree is therefore estimated by that of its graph limit; without the degree condition on the graphs the conclusion fails (Remark 4.32 of the paper).
--
--   Differences from the source:
--   - reading: $G_n\to W$ (Definition 2.9, convergence of homomorphism densities) → $\delta_\square(W_{G_n},W)\to0$; reason: the proof states that the assumption is equivalent to (4.144), $\delta_\square(W_{G_n},W)\to0$, and uses only (4.144); the introduction (p.2) describes convergence the same way; the equivalence is the standard theorem of Borgs–Chayes–Lovász–Sós–Vesztergombi, not proved in the paper.
--   - encoding: the infimum in $\delta_\square$ over all probability spaces → over probability spaces in the universe `Type (max u v)`; reason: every common space pushes forward to a coupling on $\Omega_1\times\Omega_2$, which lies in that universe and has no larger cut norm, so the value is the same.
--   - encoding: graphs $G_n$ → graphs on `Fin (N n)` with $|G_n|=N(n)$; reason: every finite graph is isomorphic to one on `Fin n`, and $h$, degrees and volumes are isomorphism invariants.
--   - encoding: $h(G_n)$ defined only without isolated vertices and $h(W)$ only for $\rho_W>0$ → total definitions with junk value $0$; reason: (4.142) with $c>0$ excludes isolated vertices for large $n$, the limit ignores finitely many $n$, and $k_W\ge c>0$ gives $\rho_W>0$.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Theorem 4.33, (4.142)–(4.144), p.50

import Mathlib
import Definitions.Def_GraphonCheeger_cutDist
import Definitions.Def_GraphonCheeger_stepGraphon
import Definitions.Def_GraphonCheeger_cheegerG
import Definitions.Def_GraphonCheeger_cheegerW

open MeasureTheory Filter Topology

namespace GraphonCheeger

/-- Theorem 4.33, p.50 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `G_n` be graphs with `|G_n| → ∞` and `G_n → W` for a graphon
`W`. Assume that for some `c > 0`, `d_min(G_n) ≥ c|G_n|` (4.142) for all sufficiently large `n`.
Then `k_W ≥ c` a.e. and `h(G_n) → h(W)` (4.143), where `h(W)` is the mixed Cheeger constant.

**Formalization Note.**
* `G n` is a graph on `Fin (N n)`, so `|G_n| = N n`; `W` lives on an arbitrary probability
  space `(Ω, µ)`.
* `G_n → W` is read as `δ_□(W_{G_n}, W) → 0` for the step graphons `W_{G_n}` on `[0, 1]`; this
  is the form (4.144) the proof uses ("the assumption `G_n → W` is equivalent to
  `δ_□(W_{G_n}, W) → 0`", p.50).
* (4.142) is `∀ v, c·N n ≤ d_v` eventually in `n`. -/
theorem theorem_4_33 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Ω → ℝ) (hW : IsGraphon W)
    (N : ℕ → ℕ) (G : (n : ℕ) → SimpleGraph (Fin (N n))) [∀ n, DecidableRel (G n).Adj]
    (hN : Tendsto N atTop atTop)
    (hconv : Tendsto (fun n => cutDist volume (stepGraphon (G n)) μ W) atTop (𝓝 0))
    (c : ℝ) (hc : 0 < c)
    (hdeg : ∀ᶠ n in atTop, ∀ v : Fin (N n), c * (N n : ℝ) ≤ ((G n).degree v : ℝ)) :
    (∀ᵐ x ∂μ, c ≤ degFun μ W x) ∧
    Tendsto (fun n => cheegerG (G n)) atTop (𝓝 (cheegerW μ W)) := by sorry

end GraphonCheeger
