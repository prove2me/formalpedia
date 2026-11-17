-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_15
-- name    : GraphonCheeger.Supplement.theorem_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:32:08.836206+00:00
-- url     : https://prove2.me/theorems/d59b3966-c271-4a03-94d2-704770c50f24
-- title:
--   Theorem 4.15 — $\mathrm{MS}_k(G_n)\to\mathrm{MS}_k(W)$ when $G_n\to W$
-- statement:
--   Let $k\ge2$ be fixed and let $W$ be a graphon on an arbitrary probability space $(\Omega,\mathcal F,\mu)$. If $(G_n)$ is a sequence of graphs with $|G_n|\to\infty$ and $G_n\to W$, then
--   $$
--   \mathrm{MS}_k(G_n)\longrightarrow\mathrm{MS}_k(W),
--   $$
--   where $\mathrm{MS}_k(G_n)$ is the normalised minimum balanced $k$-section (4.42) and $\mathrm{MS}_k(W)=\mathrm{MS}_{k,\mathrm{mix}}(W)$.
--
--   Minimum $k$-section, and in particular minimum bisection ($k=2$), is therefore continuous along convergent dense graph sequences, with the mixed graphon value as limit.
--
--   Differences from the source:
--   - encoding: Gₙ → W for uncoloured graphs with |Gₙ| → ∞ → GConv N G μ W: N n → ∞ and t(F, Gₙ) → t(F, W) for every finite simple graph F (graphs on Fin (N n)); reason: Definition 2.9 with Theorem 2.11(iii) for κ = 1; this is the paper's definition, not the δ□(W_{Gₙ}, W) → 0 reading of the published base goal
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.15, p.40 (PDF p.40)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens
import Definitions.Def_GraphonCheeger_Supplement_kSection

open MeasureTheory Filter Topology

universe u

namespace GraphonCheeger.Supplement

/-- Theorem 4.15, p.40 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `k ≥ 2` be fixed and let `W` be a graphon on an arbitrary probability
space `(Ω, F, µ)`. If `G_n` is a sequence of graphs with `|G_n| → ∞` and `G_n → W`, then
`MS_k(G_n) → MS_k(W)` (4.70).

**Formalization Note.** `G n` is a graph on `Fin (N n)`. `|G_n| → ∞` and `G_n → W` together are
`GConv N G µ W`: `N n → ∞` and `t(F, G_n) → t(F, W)` for every finite simple graph `F`
(Def. 2.9, `κ = 1`). `MS_k(G)` is (4.42) and `MS_k(W) = MS_{k,mix}(W)` (4.49). -/
theorem theorem_4_15 (k : ℕ) (hk : 2 ≤ k) {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Ω → Ω → ℝ) (hW : IsGraphon W)
    (N : ℕ → ℕ) (G : (n : ℕ) → SimpleGraph (Fin (N n))) (hconv : GConv N G μ W) :
    Tendsto (fun n => minSectionG k (G n)) atTop (𝓝 (minSectionMix k μ W)) := by sorry

end GraphonCheeger.Supplement
