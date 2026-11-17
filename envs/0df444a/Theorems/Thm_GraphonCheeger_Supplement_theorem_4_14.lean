-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_14
-- name    : GraphonCheeger.Supplement.theorem_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:31:34.855736+00:00
-- url     : https://prove2.me/theorems/af146ab9-4666-4cf6-b5a0-5bce43cc4ca4
-- title:
--   Theorem 4.14 — $|\mathrm{MS}_k(W_1)-\mathrm{MS}_k(W_2)|\le\binom k2\,\delta_\square(W_1,W_2)$
-- statement:
--   Fix $k\ge2$, and let $W_1$ and $W_2$ be graphons on possibly different probability spaces. Then
--   $$
--   \bigl|\mathrm{MS}_k(W_1)-\mathrm{MS}_k(W_2)\bigr|\le\binom k2\,\delta_\square(W_1,W_2),
--   $$
--   where $\mathrm{MS}_k=\mathrm{MS}_{k,\mathrm{mix}}$. In particular, if $W_1\cong W_2$ then $\mathrm{MS}_k(W_1)=\mathrm{MS}_k(W_2)$. Consequently, if $W_n\to W$ in cut distance, then $\mathrm{MS}_k(W_n)\to\mathrm{MS}_k(W)$.
--
--   The mixed minimum $k$-section is a Lipschitz functional on graphons with the cut distance and is well defined on graph limits; Theorem 4.15 transfers this to graph sequences.
--
--   **Formalization Note** $\delta_\square$ is the base `cutDist`; the constant is $\binom k2=k(k-1)/2$ as printed. In the sequential clause each $W_n$ lives on its own probability space.
--
--   Differences from the source:
--   - encoding: graphons on arbitrary probability spaces → Ω₁ : Type u, Ω₂ : Type v with probability measures; reason: universe-polymorphic types cover every probability space
--   - encoding: equivalent uncoloured graphons → GEquiv: equal t(F, ·) for every finite simple graph F (Definition 2.6 with κ = 1, ψ₁ ≡ 1); reason: an uncoloured graphon is a 1-coloured one (p.6); condition (i) of Lemma 2.5
--   - encoding: graphons Wₙ → W in cut distance, on possibly different probability spaces → each Wₙ on its own probability space (Ωs n, μs n), W on (Ω, μ); cutDist (Wₙ, W) → 0; reason: sequences of graphons over varying spaces, as in the published base Theorem 4.31
--   - reading: "In other words, … is a continuous functional on the set of graphons equipped with cut distance, and thus also on the quotient space Ŵ of graph limits" → not stated separately; reason: the sentence restates the sequential clause (δ□ is a pseudometric and Ŵ its metric quotient)
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.14, p.40 (PDF p.40)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens
import Definitions.Def_GraphonCheeger_Supplement_kSection
import Definitions.Def_GraphonCheeger_cutDist

open MeasureTheory Filter Topology

universe u v

namespace GraphonCheeger.Supplement

/-- Theorem 4.14, p.40 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): if `W₁` and `W₂` are graphons on possibly different probability spaces, then
`|MS_k(W₁) − MS_k(W₂)| ≤ (k choose 2) δ_□(W₁, W₂)` (4.67). In particular, if `W₁ ≅ W₂`, then
`MS_k(W₁) = MS_k(W₂)`. Consequently, if `W_n → W` in cut distance, then `MS_k(W_n) → MS_k(W)`.

**Formalization Note.** `k ≥ 2` is fixed (§4.2). `MS_k = MS_{k,mix}` (4.49), `δ_□` the base
`cutDist`, `≅` is `GEquiv` (Def. 2.6, `κ = 1`). In the sequential clause `W_n` lives on
`(Ωs n, µs n)`. The "in other words" sentence restates the sequential clause. -/
theorem theorem_4_14 (k : ℕ) (hk : 2 ≤ k) {Ω₁ : Type u} {Ω₂ : Type v} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (μ₂ : Measure Ω₂)
    [IsProbabilityMeasure μ₂] (W₁ : Ω₁ → Ω₁ → ℝ) (W₂ : Ω₂ → Ω₂ → ℝ) (hW₁ : IsGraphon W₁)
    (hW₂ : IsGraphon W₂) :
    |minSectionMix k μ₁ W₁ - minSectionMix k μ₂ W₂| ≤ (k.choose 2 : ℝ) * cutDist μ₁ W₁ μ₂ W₂ ∧
    (GEquiv μ₁ W₁ μ₂ W₂ → minSectionMix k μ₁ W₁ = minSectionMix k μ₂ W₂) ∧
    ∀ (Ωs : ℕ → Type u) [∀ n, MeasurableSpace (Ωs n)] (μs : ∀ n, Measure (Ωs n))
      [∀ n, IsProbabilityMeasure (μs n)] (Ws : ∀ n, Ωs n → Ωs n → ℝ), (∀ n, IsGraphon (Ws n)) →
      Tendsto (fun n => cutDist (μs n) (Ws n) μ₂ W₂) atTop (𝓝 0) →
      Tendsto (fun n => minSectionMix k (μs n) (Ws n)) atTop (𝓝 (minSectionMix k μ₂ W₂)) := by sorry

end GraphonCheeger.Supplement
