-- Prove2me | Theorems.Thm_GraphonCheeger_lemma_4_30
-- name    : GraphonCheeger.lemma_4_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:57:44.26877+00:00
-- url     : https://prove2.me/theorems/8681457f-ecc0-4b6c-ae0c-d70db0de226f
-- title:
--   Lemma 4.30: $\mathcal W_c$ is closed under convergence in cut distance
-- statement:
--   Let $W_n$ and $W$ be graphons, each on its own probability space, with $\delta_\square(W_n,W)\to0$ as $n\to\infty$. If $c\in[0,1]$ and $W_n\in\mathcal W_c$ for all $n$, then $W\in\mathcal W_c$.
--
--   In the graph setting this gives the first conclusion of the main theorem: a cut-distance limit of graphs with $d_{\min}\ge c|G_n|$ has degree function at least $c$ almost everywhere.
--
--   Differences from the source:
--   - encoding: the infimum in $\delta_\square$ over all probability spaces → over probability spaces in the universe `Type (max u v)` of the two graphons' spaces; reason: every common space pushes forward to a coupling on $\Omega_1\times\Omega_2$, which lies in that universe and has no larger cut norm, so the value is the same.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Lemma 4.30, p.49

import Mathlib
import Definitions.Def_GraphonCheeger_cutDist
import Definitions.Def_GraphonCheeger_InWc

open MeasureTheory Filter Topology

namespace GraphonCheeger

/-- Lemma 4.30, p.49 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W_n` and `W` be graphons with `δ_□(W_n, W) → 0`. If
`c ∈ [0, 1]` and all `W_n ∈ W_c`, then `W ∈ W_c` (`W_c` is closed).

**Formalization Note.** Each `W_n` lives on its own probability space `(Ωs n, μs n)`, and `W` on
a further space `(Ω, μ)`. -/
theorem lemma_4_30 {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)] (μs : ∀ n, Measure (Ωs n))
    [∀ n, IsProbabilityMeasure (μs n)] (Ws : ∀ n, Ωs n → Ωs n → ℝ) (hWs : ∀ n, IsGraphon (Ws n))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Ω → ℝ) (hW : IsGraphon W)
    (hconv : Tendsto (fun n => cutDist (μs n) (Ws n) μ W) atTop (𝓝 0))
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (hWc : ∀ n, InWc (μs n) (Ws n) c) :
    InWc μ W c := by sorry

end GraphonCheeger
