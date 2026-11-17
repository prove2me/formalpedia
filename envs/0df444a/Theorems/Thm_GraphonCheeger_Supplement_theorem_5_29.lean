-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_5_29
-- name    : GraphonCheeger.Supplement.theorem_5_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:38:00.322011+00:00
-- url     : https://prove2.me/theorems/a6d6e75e-c1ea-43d9-977c-47824eba6443
-- title:
--   Theorem 5.29 — $q^*(G_n)\to\hat q^*(W)$ when $G_n\to W$ and $\rho_W>0$
-- statement:
--   Let $(G_n)_{n\ge1}$ be graphs with $N_n:=|G_n|\to\infty$, and suppose $G_n\to W$, where $W$ is a graphon with $\rho_W>0$. Then
--   $$
--   \lim_{n\to\infty}q^*(G_n)=\hat q^*(W).
--   $$
--
--   Graphon modularity is the limit of graph modularity along convergent dense graph sequences, which answers the question left open by the graphon modularity of Klimm, Jones and Schaub.
--
--   Differences from the source:
--   - encoding: Gₙ → W for uncoloured graphs with |Gₙ| → ∞ → GConv N G μ W: N n → ∞ and t(F, Gₙ) → t(F, W) for every finite simple graph F (graphs on Fin (N n)); reason: Definition 2.9 with Theorem 2.11(iii) for κ = 1; this is the paper's definition, not the δ□(W_{Gₙ}, W) → 0 reading of the published base goal
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 5.29, p.69 (PDF p.69)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens
import Definitions.Def_GraphonCheeger_Supplement_graphModularity
import Definitions.Def_GraphonCheeger_Supplement_graphonModularity

open MeasureTheory Filter Topology

universe u

namespace GraphonCheeger.Supplement

/-- Theorem 5.29, p.69 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `(G_n)_{n ≥ 1}` be graphs with `N_n := |G_n| → ∞`, and suppose
`G_n → W`, where `W` is a graphon with `ρ_W > 0`. Then `lim_{n→∞} q*(G_n) = q̂*(W)` (5.127).

**Formalization Note.** `G n` is a graph on `Fin (N n)`; `|G_n| → ∞` and `G_n → W` are
`GConv N G µ W` (Def. 2.9, `κ = 1`: `t(F, G_n) → t(F, W)` for every finite simple graph `F`). `W`
lives on an arbitrary probability space. -/
theorem theorem_5_29 {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Ω → ℝ) (hW : IsGraphon W) (hρ : 0 < density μ W)
    (N : ℕ → ℕ) (G : (n : ℕ) → SimpleGraph (Fin (N n))) (hconv : GConv N G μ W) :
    Tendsto (fun n => modularity (G n)) atTop (𝓝 (modW μ W)) := by sorry

end GraphonCheeger.Supplement
