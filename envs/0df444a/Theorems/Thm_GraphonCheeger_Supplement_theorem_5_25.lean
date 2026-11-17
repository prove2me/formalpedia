-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_5_25
-- name    : GraphonCheeger.Supplement.theorem_5_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:37:32.27279+00:00
-- url     : https://prove2.me/theorems/2065b87a-3fe4-4dc7-9f53-5970404d7667
-- title:
--   Theorem 5.25 — $W\mapsto\hat q^*_\kappa(W)$ is continuous at every graphon with $\rho_W>0$
-- statement:
--   Fix $\kappa\ge1$. The functional $W\mapsto\hat q^*_\kappa(W)$ is continuous at every uncoloured graphon $W$ with $\rho_W>0$: if graphons $W_n$ (on possibly different probability spaces) satisfy $\delta_\square(W_n,W)\to0$, then
--   $$
--   \hat q^*_\kappa(W_n)\to\hat q^*_\kappa(W).
--   $$
--
--   This fixed-$\kappa$ version is the main step toward Theorem 5.23.
--
--   **Formalization Note** Continuity is with respect to the cut distance (base `cutDist`, as in (5.114)), along sequences, each $W_n$ on its own probability space.
--
--   Differences from the source:
--   - reading: "the functional W ↦ q̂*_κ(W) is continuous at W" (topology not named) → δ□(Wₙ, W) → 0 ⟹ q̂*_κ(Wₙ) → q̂*_κ(W), along sequences; reason: the proof bounds the change by 4κ δ□ ((5.114)); δ□ is a pseudometric, so sequential continuity is continuity
--   - encoding: graphons Wₙ → W in cut distance, on possibly different probability spaces → each Wₙ on its own probability space (Ωs n, μs n), W on (Ω, μ); cutDist (Wₙ, W) → 0; reason: sequences of graphons over varying spaces, as in the published base Theorem 4.31
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 5.25, p.66 (PDF p.66)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_graphonModularity
import Definitions.Def_GraphonCheeger_cutDist

open MeasureTheory Filter Topology

universe u v

namespace GraphonCheeger.Supplement

/-- Theorem 5.25, p.66 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): fix `κ ≥ 1`. Then the functional `W ↦ q̂*_κ(W)` is continuous at every
uncoloured graphon `W` with `ρ_W > 0`.

**Formalization Note.** Continuity is with respect to the cut distance `δ_□` (base `cutDist`, as in
(5.114)), stated along sequences of graphons `W_n` on `(Ωs n, µs n)`. -/
theorem theorem_5_25 (κ : ℕ) (hκ : 1 ≤ κ) {Ωs : ℕ → Type u} [∀ n, MeasurableSpace (Ωs n)]
    (μs : ∀ n, Measure (Ωs n)) [∀ n, IsProbabilityMeasure (μs n)] (Ws : ∀ n, Ωs n → Ωs n → ℝ)
    (hWs : ∀ n, IsGraphon (Ws n)) {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Ω → Ω → ℝ) (hW : IsGraphon W) (hρ : 0 < density μ W)
    (hconv : Tendsto (fun n => cutDist (μs n) (Ws n) μ W) atTop (𝓝 0)) :
    Tendsto (fun n => modK κ (μs n) (Ws n)) atTop (𝓝 (modK κ μ W)) := by sorry

end GraphonCheeger.Supplement
