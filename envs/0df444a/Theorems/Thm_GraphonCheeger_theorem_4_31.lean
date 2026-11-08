-- Prove2me | Theorems.Thm_GraphonCheeger_theorem_4_31
-- name    : GraphonCheeger.theorem_4_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:01:28.584313+00:00
-- url     : https://prove2.me/theorems/f4e0d25e-2411-4149-a8da-6ad29937c549
-- title:
--   Theorem 4.31: $h$ is continuous in cut distance on $\mathcal W_c$, $c>0$
-- statement:
--   Let $W_n$ and $W$ be graphons, each on its own probability space, with $\delta_\square(W_n,W)\to0$ as $n\to\infty$. Assume that for some $c>0$, $W_n\in\mathcal W_c$ for all sufficiently large $n$. Then the mixed Cheeger constants converge:
--
--   $$h(W_n)\to h(W).$$
--
--   Differences from the source:
--   - encoding: $c>0$ with $W_n\in\mathcal W_c$, where Definition 4.28 requires $c\in[0,1]$ → any real $c>0$; reason: for $c>1$ the hypothesis cannot hold (a graphon has $k_W\le1$ and the measure is a probability measure), so no instance is added.
--   - encoding: the infimum in $\delta_\square$ over all probability spaces → over probability spaces in the universe `Type (max u v)` of the two graphons' spaces; reason: every common space pushes forward to a coupling on $\Omega_1\times\Omega_2$, which lies in that universe and has no larger cut norm, so the value is the same.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Theorem 4.31, (4.140), p.49

import Mathlib
import Definitions.Def_GraphonCheeger_cutDist
import Definitions.Def_GraphonCheeger_cheegerW
import Definitions.Def_GraphonCheeger_InWc

open MeasureTheory Filter Topology

namespace GraphonCheeger

/-- Theorem 4.31, p.49 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W_n` and `W` be graphons with `δ_□(W_n, W) → 0`, and assume
that for some `c > 0`, `W_n ∈ W_c` for all sufficiently large `n`. Then `h(W_n) → h(W)`
(4.140), for the mixed Cheeger constant.

**Formalization Note.** Each `W_n` lives on its own probability space `(Ωs n, μs n)`. -/
theorem theorem_4_31 {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)] (μs : ∀ n, Measure (Ωs n))
    [∀ n, IsProbabilityMeasure (μs n)] (Ws : ∀ n, Ωs n → Ωs n → ℝ) (hWs : ∀ n, IsGraphon (Ws n))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Ω → ℝ) (hW : IsGraphon W)
    (hconv : Tendsto (fun n => cutDist (μs n) (Ws n) μ W) atTop (𝓝 0))
    (c : ℝ) (hc : 0 < c) (hWc : ∀ᶠ n in atTop, InWc (μs n) (Ws n) c) :
    Tendsto (fun n => cheegerW (μs n) (Ws n)) atTop (𝓝 (cheegerW μ W)) := by sorry

end GraphonCheeger
