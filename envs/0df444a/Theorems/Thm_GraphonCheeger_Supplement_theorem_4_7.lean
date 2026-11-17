-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_7
-- name    : GraphonCheeger.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:29:36.616724+00:00
-- url     : https://prove2.me/theorems/b16e7103-e530-4240-b41f-db115d2e262e
-- title:
--   Theorem 4.7 — $|\mathrm{MC}(W_1)-\mathrm{MC}(W_2)|\le\delta_\square(W_1,W_2)$
-- statement:
--   Let $W_1$ and $W_2$ be graphons on possibly different probability spaces. Then
--   $$
--   \bigl|\mathrm{MC}(W_1)-\mathrm{MC}(W_2)\bigr|\le\delta_\square(W_1,W_2),
--   $$
--   where $\mathrm{MC}=\mathrm{MC}_{\mathrm{mix}}$ and $\delta_\square$ is the cut distance. Hence, if graphons $W_n\to W$ in cut distance, then $\mathrm{MC}(W_n)\to\mathrm{MC}(W)$.
--
--   The mixed maximum cut is thus a $1$-Lipschitz, hence continuous, functional on graphons with the cut distance and on graph limits; this gives Corollary 4.8 for convergent graph sequences.
--
--   **Formalization Note** $\delta_\square$ is the base `cutDist` (A.5). In the sequential clause each $W_n$ lives on its own probability space.
--
--   Differences from the source:
--   - encoding: graphons on arbitrary probability spaces → Ω₁ : Type u, Ω₂ : Type v with probability measures; reason: universe-polymorphic types cover every probability space
--   - encoding: graphons Wₙ → W in cut distance, on possibly different probability spaces → each Wₙ on its own probability space (Ωs n, μs n), W on (Ω, μ); cutDist (Wₙ, W) → 0; reason: sequences of graphons over varying spaces, as in the published base Theorem 4.31
--   - reading: "In other words, … is a continuous functional on the set of graphons equipped with cut distance, and thus also on the quotient space Ŵ of graph limits" → not stated separately; reason: the sentence restates the sequential clause (δ□ is a pseudometric and Ŵ its metric quotient)
--   - encoding: mixed 2-colouring Ψ = (ψ, 1 − ψ) → ψ : Ω → [0, 1] measurable (base IsColouring); C(W, Ψ) is the base cutVal; reason: the identification the paper makes (pp.31–32)
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.7, p.35 (PDF p.35)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_maxCut
import Definitions.Def_GraphonCheeger_cutDist

open MeasureTheory Filter Topology

universe u v

namespace GraphonCheeger.Supplement

/-- Theorem 4.7, p.35 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): if `W₁` and `W₂` are graphons, then `|MC(W₁) − MC(W₂)| ≤ δ_□(W₁, W₂)`
(4.35). Hence, if `W_n → W` in cut distance, then `MC(W_n) → MC(W)`; i.e. `MC = MC_mix` is a
continuous functional on graphons with the cut distance, and thus also on the quotient space `Ŵ` of
graph limits.

**Formalization Note.** `MC = MC_mix` (4.32), `δ_□` is the base `cutDist` (A.5). The graphons live on
possibly different probability spaces; in the sequential clause `W_n` lives on `(Ωs n, µs n)`. The
"in other words" sentence restates the sequential clause and is not a separate claim. -/
theorem theorem_4_7 {Ω₁ : Type u} {Ω₂ : Type v} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
    (W₁ : Ω₁ → Ω₁ → ℝ) (W₂ : Ω₂ → Ω₂ → ℝ) (hW₁ : IsGraphon W₁) (hW₂ : IsGraphon W₂) :
    |maxCutMix μ₁ W₁ - maxCutMix μ₂ W₂| ≤ cutDist μ₁ W₁ μ₂ W₂ ∧
    ∀ (Ωs : ℕ → Type u) [∀ n, MeasurableSpace (Ωs n)] (μs : ∀ n, Measure (Ωs n))
      [∀ n, IsProbabilityMeasure (μs n)] (Ws : ∀ n, Ωs n → Ωs n → ℝ), (∀ n, IsGraphon (Ws n)) →
      Tendsto (fun n => cutDist (μs n) (Ws n) μ₂ W₂) atTop (𝓝 0) →
      Tendsto (fun n => maxCutMix (μs n) (Ws n)) atTop (𝓝 (maxCutMix μ₂ W₂)) := by sorry

end GraphonCheeger.Supplement
