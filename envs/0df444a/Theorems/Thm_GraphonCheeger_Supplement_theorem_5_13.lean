-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_5_13
-- name    : GraphonCheeger.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:35:05.78898+00:00
-- url     : https://prove2.me/theorems/fa97f14a-b625-4ea8-acba-be8ea40de23e
-- title:
--   Theorem 5.13 — $\hat q^*_\kappa$ and $\hat q^*$ are invariant under equivalence of graphons
-- statement:
--   Let $W_1$ and $W_2$ be equivalent uncoloured graphons, on possibly different probability spaces. Then
--   $$
--   \hat q^*_\kappa(W_1)=\hat q^*_\kappa(W_2)\quad\text{for every }\kappa\ge1,\qquad \hat q^*(W_1)=\hat q^*(W_2).
--   $$
--   Consequently $\hat q^*_\kappa$ and $\hat q^*$ are well defined on graph limits.
--
--   This is the reason for defining graphon modularity with mixed colourings: the pure version is not invariant (Example 5.20).
--
--   Differences from the source:
--   - encoding: equivalent uncoloured graphons → GEquiv: equal t(F, ·) for every finite simple graph F (Definition 2.6 with κ = 1, ψ₁ ≡ 1); reason: an uncoloured graphon is a 1-coloured one (p.6); condition (i) of Lemma 2.5
--   - encoding: graphons on arbitrary probability spaces → Ω₁ : Type u, Ω₂ : Type v with probability measures; reason: universe-polymorphic types cover every probability space
--   - reading: "Consequently, q̂*_κ(Ŵ) and q̂*(Ŵ) are well-defined for graph limits Ŵ" → not stated separately; reason: the sentence restates the invariance (graph limits are equivalence classes of graphons, Theorem 2.12)
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 5.13, p.59 (PDF p.59)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens
import Definitions.Def_GraphonCheeger_Supplement_graphonModularity

open MeasureTheory

universe u v

namespace GraphonCheeger.Supplement

/-- Theorem 5.13, p.59 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): if `W₁` and `W₂` are two equivalent uncoloured graphons, then
`q̂*_κ(W₁) = q̂*_κ(W₂)` for every `κ ≥ 1`, and thus `q̂*(W₁) = q̂*(W₂)`. Consequently `q̂*_κ(Ŵ)` and
`q̂*(Ŵ)` are well defined for graph limits `Ŵ`.

**Formalization Note.** `≅` of uncoloured graphons is `GEquiv` (Def. 2.6, `κ = 1`); the graphons
live on possibly different probability spaces. The last sentence restates the invariance. -/
theorem theorem_5_13 {Ω₁ : Type u} {Ω₂ : Type v} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
    (W₁ : Ω₁ → Ω₁ → ℝ) (W₂ : Ω₂ → Ω₂ → ℝ) (hW₁ : IsGraphon W₁) (hW₂ : IsGraphon W₂)
    (hequiv : GEquiv μ₁ W₁ μ₂ W₂) :
    (∀ κ : ℕ, 1 ≤ κ → modK κ μ₁ W₁ = modK κ μ₂ W₂) ∧ modW μ₁ W₁ = modW μ₂ W₂ := by sorry

end GraphonCheeger.Supplement
