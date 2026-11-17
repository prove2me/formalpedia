-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_5_14
-- name    : GraphonCheeger.Supplement.theorem_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:35:38.250809+00:00
-- url     : https://prove2.me/theorems/65382130-506b-47f9-97d7-ed8d6d604df0
-- title:
--   Theorem 5.14 — $\hat q^*_\kappa$ is a maximum; the supremum over $\kappa$ in $\hat q^*$ need not be attained
-- statement:
--   1. For every uncoloured graphon $W$ on a probability space and every $\kappa\ge1$, the supremum over $\Psi\in\Lambda_\kappa$ in (5.34) is attained: there is a $\kappa$-colouring $\Psi$ with $\hat q(W,\Psi)=\hat q^*_\kappa(W)$.
--   2. There exists an uncoloured graphon $W$ for which the supremum over $\kappa$ in (5.35) is not attained, i.e.
--   $$
--   \hat q^*_\kappa(W)<\hat q^*(W)\quad\text{for every }\kappa\ge1 .
--   $$
--
--   The paper's example (Example 5.16) is the limit of disjoint unions of cliques of sizes $n/2,n/4,\dots$; graphon modularity may need infinitely many communities.
--
--   **Formalization Note** The first clause is stated for graphons on every probability space `Ω : Type u`; the graphon of the second clause lives on some probability space `Ω : Type`. Since $\hat q^*_\kappa(W)\le\hat q^*(W)$ for every $\kappa$, "not attained" is the strict inequality for every $\kappa$.
--
--   Differences from the source:
--   - encoding: "the supremum over κ in (5.35) is not attained" → q̂*_κ(W) < q̂*(W) for every κ ≥ 1; reason: q̂*(W) is the supremum of the q̂*_κ(W), so it is attained iff it equals one of them
--   - encoding: there exists an uncoloured graphon W (on some probability space) → ∃ (Ω : Type) with a probability measure and a graphon; reason: a probability space in the lowest universe exists for the paper's example ([0, 1])
--   - encoding: colourings Ψ : Ω → Δκ, colours [κ]; pure colourings χ : Ω → [κ] → Ψ : Ω → Fin κ → ℝ with measurable nonnegative coordinates summing to 1 (IsKColouring); pure χ measurable with the point-mass colouring ofColour χ; reason: the same objects (Definition 2.1, p.7), with colours numbered 0, …, κ − 1
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 5.14, p.59 (PDF p.59)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_graphonModularity

open MeasureTheory

universe u

namespace GraphonCheeger.Supplement

/-- Theorem 5.14, p.59 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for every uncoloured graphon `W` and `κ ≥ 1`, the supremum over
`Ψ ∈ Λ_κ` in (5.34) is attained (so it is a maximum). However, there exists an uncoloured graphon
`W` such that the supremum over `κ` in (5.35) is not attained.

**Formalization Note.** The first clause is stated for graphons on every probability space
`Ω : Type u`. "The supremum over `κ` is not attained" is `q̂*_κ(W) < q̂*(W)` for every `κ ≥ 1`; the
graphon of the second clause lives on some probability space `Ω : Type`. -/
theorem theorem_5_14 :
    (∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ), IsGraphon W → ∀ κ : ℕ, 1 ≤ κ →
        ∃ Ψ : Ω → Fin κ → ℝ, IsKColouring Ψ ∧ qhat μ W Ψ = modK κ μ W) ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (W : Ω → Ω → ℝ),
      IsProbabilityMeasure μ ∧ IsGraphon W ∧ ∀ κ : ℕ, 1 ≤ κ → modK κ μ W < modW μ W := by sorry

end GraphonCheeger.Supplement
