-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_5_23
-- name    : GraphonCheeger.Supplement.theorem_5_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:37:07.456486+00:00
-- url     : https://prove2.me/theorems/a7b899c5-79e5-445e-a69c-4e29c8ae67c4
-- title:
--   Theorem 5.23 — $W\mapsto\hat q^*(W)$ is continuous at every graphon with $\rho_W>0$
-- statement:
--   The functional $W\mapsto\hat q^*(W)$ is continuous at every uncoloured graphon $W$ with $\rho_W>0$: if graphons $W_n$ (on possibly different probability spaces) satisfy $\delta_\square(W_n,W)\to0$, then
--   $$
--   \hat q^*(W_n)\to\hat q^*(W).
--   $$
--
--   Remark 5.24 shows the condition $\rho_W>0$ cannot be dropped. This is the continuity used for Theorem 5.29.
--
--   **Formalization Note** Continuity is with respect to the cut distance (base `cutDist`), the topology of the proof ((5.114)); it is stated along sequences, each $W_n$ on its own probability space.
--
--   Differences from the source:
--   - reading: "the functional W ↦ q̂*(W) is continuous at W" (topology not named) → δ□(Wₙ, W) → 0 ⟹ q̂*(Wₙ) → q̂*(W), along sequences; reason: the proof works in cut distance ((5.114)) and Remark 5.24 uses cut-norm convergence; δ□ is a pseudometric, so sequential continuity is continuity
--   - encoding: graphons Wₙ → W in cut distance, on possibly different probability spaces → each Wₙ on its own probability space (Ωs n, μs n), W on (Ω, μ); cutDist (Wₙ, W) → 0; reason: sequences of graphons over varying spaces, as in the published base Theorem 4.31
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 5.23, p.66 (PDF p.66)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_graphonModularity
import Definitions.Def_GraphonCheeger_cutDist

open MeasureTheory Filter Topology

universe u v

namespace GraphonCheeger.Supplement

/-- Theorem 5.23, p.66 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): the functional `W ↦ q̂*(W)` is continuous at every uncoloured graphon `W`
with `ρ_W > 0`.

**Formalization Note.** Continuity is with respect to the cut distance `δ_□` (base `cutDist`), the
topology used in the proof ((5.114), Remark 5.24), on graphons over all probability spaces, stated
along sequences: `W_n` lives on `(Ωs n, µs n)`, and `δ_□(W_n, W) → 0` implies
`q̂*(W_n) → q̂*(W)`. -/
theorem theorem_5_23 {Ωs : ℕ → Type u} [∀ n, MeasurableSpace (Ωs n)] (μs : ∀ n, Measure (Ωs n))
    [∀ n, IsProbabilityMeasure (μs n)] (Ws : ∀ n, Ωs n → Ωs n → ℝ) (hWs : ∀ n, IsGraphon (Ws n))
    {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Ω → ℝ) (hW : IsGraphon W) (hρ : 0 < density μ W)
    (hconv : Tendsto (fun n => cutDist (μs n) (Ws n) μ W) atTop (𝓝 0)) :
    Tendsto (fun n => modW (μs n) (Ws n)) atTop (𝓝 (modW μ W)) := by sorry

end GraphonCheeger.Supplement
