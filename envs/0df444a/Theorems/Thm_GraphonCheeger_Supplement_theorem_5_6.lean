-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_5_6
-- name    : GraphonCheeger.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:34:03.164696+00:00
-- url     : https://prove2.me/theorems/ffa65368-ccdd-4b28-b05e-9733d90b5b37
-- title:
--   Theorem 5.6 — $\hat q$ is invariant under $\cong$ and continuous on $\widehat{\mathcal W}_\kappa$ where $\rho>0$
-- statement:
--   Fix $\kappa\ge1$.
--
--   1. If two $\kappa$-coloured graphons $W_1$ and $W_2$ are equivalent, then $\hat q(W_1)=\hat q(W_2)$, where $\hat q$ is the modularity score (5.3). Hence $\hat q$ is well defined on coloured graph limits.
--   2. The functional $W\mapsto\hat q_\kappa(W)$ so defined on $\widehat{\mathcal W}_\kappa$ is continuous at every $\kappa$-coloured graph limit $W$ with $\rho_W>0$.
--
--   The modularity score of a fixed colouring is thus a graph-limit parameter, a step toward the continuity of graphon modularity in §5.2.
--
--   **Formalization Note** Coloured graph limits are $\widehat{\mathcal W}_\kappa\subset\mathbb R^L$ with the subspace topology. The functional is a map $f$ on $\mathbb R^L$ with $f(\tau(W,\Psi))=\hat q(W,\Psi)$ for every coloured graphon (on probability spaces `Ω : Type u`), and continuity is `ContinuousWithinAt f Ŵ_κ` at every point $\tau(W,\Psi)$ with $\rho_W>0$. Every point of $\widehat{\mathcal W}_\kappa$ is such a $\tau(W,\Psi)$ (Theorem 2.11(i)).
--
--   Differences from the source:
--   - encoding: the functional W ↦ q̂κ(W) on Ŵκ, continuous at every limit W with ρ_W > 0 → ∃ f : ℝ^L → ℝ with f(τ(W, Ψ)) = q̂(W, Ψ) for all coloured graphons, ContinuousWithinAt f Ŵκ (τ(W, Ψ)) whenever ρ_W > 0; reason: every point of Ŵκ is τ of a coloured graphon (Theorem 2.11(i)) and ρ_W is determined by τ (5.11), so f restricted to Ŵκ is the page's functional
--   - encoding: W₁ ≅ W₂ (Definition 2.6: one, and thus all, of the conditions of Lemma 2.5) → CEquiv: t(F, W₁) = t(F, W₂) for every coloured graph F; reason: condition (i) of Lemma 2.5, which Definition 2.6 lists as equivalent to the others
--   - encoding: test graphs F ∈ U (unlabelled coloured graphs); limits as points of [0,1]^U → labelled coloured graphs on Fin (n+1) (LIdx κ); points of ℝ^L with the product topology; reason: t(F, ·) is invariant under relabelling (p.8), so equalities, convergence and limits over L and U agree; ℝ^L only changes the ambient space
--   - encoding: colourings Ψ : Ω → Δκ, colours [κ]; pure colourings χ : Ω → [κ] → Ψ : Ω → Fin κ → ℝ with measurable nonnegative coordinates summing to 1 (IsKColouring); pure χ measurable with the point-mass colouring ofColour χ; reason: the same objects (Definition 2.1, p.7), with colours numbered 0, …, κ − 1
--   - encoding: κ ≥ 1 (Definition 2.1) → [NeZero κ]; reason: the same condition
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 5.6, p.56 (PDF p.56)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens
import Definitions.Def_GraphonCheeger_Supplement_graphonModularity

open MeasureTheory

universe u v

namespace GraphonCheeger.Supplement

/-- Theorem 5.6, p.56 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): fix `κ ≥ 1`. If `W₁` and `W₂` are two equivalent `κ`-coloured graphons, then
`q̂(W₁) = q̂(W₂)`; i.e. `q̂` is well defined on coloured graph limits. Furthermore, the functional
`W ↦ q̂_κ(W)` is continuous at every `κ`-coloured graph limit `W` with `ρ_W > 0`.

**Formalization Note.**
* `q̂(W, Ψ)` is (5.3) (`qhat`), `≅` is Definition 2.6 (`CEquiv`), and graph limits are
  `Ŵ_κ = GraphLimitSpace κ ⊂ ℝ^L` (Def. 3.5 (W1)), with the subspace topology.
* The functional on `Ŵ_κ` is a map `f` on the ambient `ℝ^L` with `f(τ(W, Ψ)) = q̂(W, Ψ)` for every
  coloured graphon (probability spaces `Ω : Type u`); its continuity is continuity within `Ŵ_κ` at
  every point `τ(W, Ψ)` with `ρ_W > 0`. Every point of `Ŵ_κ` is some `τ(W, Ψ)` (Theorem 2.11(i)),
  so the restriction of `f` to `Ŵ_κ` is the functional of the page. -/
theorem theorem_5_6 (κ : ℕ) [NeZero κ] :
    (∀ (Ω₁ : Type u) [MeasurableSpace Ω₁] (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁]
        (W₁ : Ω₁ → Ω₁ → ℝ) (Ψ₁ : Ω₁ → Fin κ → ℝ)
        (Ω₂ : Type v) [MeasurableSpace Ω₂] (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
        (W₂ : Ω₂ → Ω₂ → ℝ) (Ψ₂ : Ω₂ → Fin κ → ℝ),
        IsGraphon W₁ → IsKColouring Ψ₁ → IsGraphon W₂ → IsKColouring Ψ₂ →
        CEquiv μ₁ W₁ Ψ₁ μ₂ W₂ Ψ₂ → qhat μ₁ W₁ Ψ₁ = qhat μ₂ W₂ Ψ₂) ∧
    ∃ f : (LIdx κ → ℝ) → ℝ,
      (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ) (Ψ : Ω → Fin κ → ℝ), IsGraphon W → IsKColouring Ψ →
        f (tau μ W Ψ) = qhat μ W Ψ) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ) (Ψ : Ω → Fin κ → ℝ), IsGraphon W → IsKColouring Ψ →
        0 < density μ W → ContinuousWithinAt f (GraphLimitSpace κ) (tau μ W Ψ) := by sorry

end GraphonCheeger.Supplement
