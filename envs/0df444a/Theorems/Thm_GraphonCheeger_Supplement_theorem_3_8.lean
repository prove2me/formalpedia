-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_3_8
-- name    : GraphonCheeger.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:25:37.496196+00:00
-- url     : https://prove2.me/theorems/c1282e83-c8d7-4824-b226-6d6ac533a9c9
-- title:
--   Theorem 3.8 — uncolouring preserves $\cong$ and induces a continuous map $\widehat{\mathcal W}_\kappa\to\widehat{\mathcal W}$
-- statement:
--   Let $\kappa\ge1$. For a coloured graphon let $\iota(W,\Psi)=W$ be its uncolouring.
--
--   1. If two $\kappa$-coloured graphons $W_1$ and $W_2$ are equivalent, then so are the uncoloured graphons $\iota(W_1)$ and $\iota(W_2)$.
--   2. Hence uncolouring is well defined on graph limits: there is a map $\widehat{\mathcal W}_\kappa\to\widehat{\mathcal W}$ sending the limit of every coloured graphon $(W,\Psi)$ to the limit of $W$, and this map is continuous.
--
--   Uncolouring connects the coloured framework to classical graph limits; it is used in the proof of Theorem 2.20.
--
--   **Formalization Note** Uncoloured graphons and limits are the case $\kappa=1$ (`trivCol`, `GraphLimitSpace 1`). The induced map is a function $f$ on $\mathbb R^L$ with $f(\tau(W,\Psi))=\tau(W)$ for every coloured graphon on a probability space `Ω : Type u`, which maps $\widehat{\mathcal W}_\kappa$ into $\widehat{\mathcal W}$ and is continuous on $\widehat{\mathcal W}_\kappa$. Every point of $\widehat{\mathcal W}_\kappa$ is some $\tau(W,\Psi)$ (Theorem 2.11(i)), so $f$ restricted to $\widehat{\mathcal W}_\kappa$ is the uncolouring map.
--
--   Differences from the source:
--   - encoding: a mapping Ŵκ → Ŵ of coloured to uncoloured graph limits, continuous → ∃ f : ℝ^{L_κ} → ℝ^{L_1} with f(τ(W, Ψ)) = τ(W) for every coloured graphon, MapsTo f Ŵκ Ŵ₁, ContinuousOn f Ŵκ; reason: every point of Ŵκ is τ of a coloured graphon (Theorem 2.11(i)), so f restricted to Ŵκ is the uncolouring map and conversely
--   - encoding: W₁ ≅ W₂ (Definition 2.6: one, and thus all, of the conditions of Lemma 2.5) → CEquiv: t(F, W₁) = t(F, W₂) for every coloured graph F; reason: condition (i) of Lemma 2.5, which Definition 2.6 lists as equivalent to the others
--   - encoding: equivalent uncoloured graphons → GEquiv: equal t(F, ·) for every finite simple graph F (Definition 2.6 with κ = 1, ψ₁ ≡ 1); reason: an uncoloured graphon is a 1-coloured one (p.6); condition (i) of Lemma 2.5
--   - encoding: test graphs F ∈ U (unlabelled coloured graphs); limits as points of [0,1]^U → labelled coloured graphs on Fin (n+1) (LIdx κ); points of ℝ^L with the product topology; reason: t(F, ·) is invariant under relabelling (p.8), so equalities, convergence and limits over L and U agree; ℝ^L only changes the ambient space
--   - encoding: colourings Ψ : Ω → Δκ, colours [κ]; pure colourings χ : Ω → [κ] → Ψ : Ω → Fin κ → ℝ with measurable nonnegative coordinates summing to 1 (IsKColouring); pure χ measurable with the point-mass colouring ofColour χ; reason: the same objects (Definition 2.1, p.7), with colours numbered 0, …, κ − 1
--   - encoding: κ ≥ 1 (Definition 2.1) → [NeZero κ]; reason: the same condition
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 3.8, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens

open MeasureTheory

universe u v

namespace GraphonCheeger.Supplement

/-- Theorem 3.8, p.22 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): if two coloured graphons `W₁` and `W₂` are equivalent, then so are the
uncoloured graphons `ι(W₁)` and `ι(W₂)`, where `ι(W, Ψ) = W`. Hence uncolouring is well defined for
graph limits and defines, for every `κ`, a mapping `Ŵ_κ → Ŵ` of coloured to uncoloured graph
limits; furthermore, this mapping is continuous.

**Formalization Note.**
* Uncoloured graphons and graph limits are the case `κ = 1` (only colouring `ψ_1 ≡ 1`,
  `trivCol`), so `Ŵ = GraphLimitSpace 1` and `ι(W₁) ≅ ι(W₂)` is `GEquiv`.
* The induced map is stated as a map `f` on the ambient `ℝ^L ⊇ Ŵ_κ` with `f(τ(W, Ψ)) = τ(W)` for
  every coloured graphon (on probability spaces `Ω : Type u`); `f` maps `Ŵ_κ` into `Ŵ` and is
  continuous on `Ŵ_κ` (subspace topology). Since every point of `Ŵ_κ` is some `τ(W, Ψ)`
  (Theorem 2.11(i)), the restriction of `f` to `Ŵ_κ` is the uncolouring map.
* `κ ≥ 1` is `[NeZero κ]`. -/
theorem theorem_3_8 (κ : ℕ) [NeZero κ] :
    (∀ (Ω₁ : Type u) [MeasurableSpace Ω₁] (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁]
        (W₁ : Ω₁ → Ω₁ → ℝ) (Ψ₁ : Ω₁ → Fin κ → ℝ)
        (Ω₂ : Type v) [MeasurableSpace Ω₂] (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
        (W₂ : Ω₂ → Ω₂ → ℝ) (Ψ₂ : Ω₂ → Fin κ → ℝ),
        IsGraphon W₁ → IsKColouring Ψ₁ → IsGraphon W₂ → IsKColouring Ψ₂ →
        CEquiv μ₁ W₁ Ψ₁ μ₂ W₂ Ψ₂ → GEquiv μ₁ W₁ μ₂ W₂) ∧
    ∃ f : (LIdx κ → ℝ) → (LIdx 1 → ℝ),
      Set.MapsTo f (GraphLimitSpace κ) (GraphLimitSpace 1) ∧ ContinuousOn f (GraphLimitSpace κ) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ) (Ψ : Ω → Fin κ → ℝ), IsGraphon W → IsKColouring Ψ →
        f (tau μ W Ψ) = tau μ W trivCol := by sorry

end GraphonCheeger.Supplement
