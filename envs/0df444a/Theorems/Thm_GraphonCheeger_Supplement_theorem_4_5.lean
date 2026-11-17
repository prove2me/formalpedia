-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_4_5
-- name    : GraphonCheeger.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:28:50.492842+00:00
-- url     : https://prove2.me/theorems/0c6335be-fd56-47fa-81cf-e664a352b2fa
-- title:
--   Theorem 4.5 — $\mathrm{MC}_{\mathrm{mix}}$ is invariant under equivalence of graphons
-- statement:
--   Let $W_1$ and $W_2$ be graphons on arbitrary (possibly different) probability spaces. If $W_1\cong W_2$, then
--   $$
--   \mathrm{MC}_{\mathrm{mix}}(W_1)=\mathrm{MC}_{\mathrm{mix}}(W_2).
--   $$
--
--   So the mixed maximum cut $\mathrm{MC}=\mathrm{MC}_{\mathrm{mix}}$ is well defined on graph limits, which the paper shows fails for $\mathrm{MC}_{\mathrm{pure}}$ (Example 4.4).
--
--   Differences from the source:
--   - encoding: equivalent uncoloured graphons → GEquiv: equal t(F, ·) for every finite simple graph F (Definition 2.6 with κ = 1, ψ₁ ≡ 1); reason: an uncoloured graphon is a 1-coloured one (p.6); condition (i) of Lemma 2.5
--   - encoding: graphons on arbitrary probability spaces → Ω₁ : Type u, Ω₂ : Type v with probability measures; reason: universe-polymorphic types cover every probability space
--   - encoding: mixed 2-colouring Ψ = (ψ, 1 − ψ) → ψ : Ω → [0, 1] measurable (base IsColouring); C(W, Ψ) is the base cutVal; reason: the identification the paper makes (pp.31–32)
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 4.5, p.35 (PDF p.35)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens
import Definitions.Def_GraphonCheeger_Supplement_maxCut

open MeasureTheory

universe u v

namespace GraphonCheeger.Supplement

/-- Theorem 4.5, p.35 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): if `W₁` and `W₂` are two equivalent graphons (defined on arbitrary
probability spaces), then `MC_mix(W₁) = MC_mix(W₂)`.

**Formalization Note.** Equivalence of uncoloured graphons is Definition 2.6 with `κ = 1`:
equal homomorphism densities `t(F, ·)` for all finite simple graphs `F` (`GEquiv`). -/
theorem theorem_4_5 {Ω₁ : Type u} {Ω₂ : Type v} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
    (W₁ : Ω₁ → Ω₁ → ℝ) (W₂ : Ω₂ → Ω₂ → ℝ) (hW₁ : IsGraphon W₁) (hW₂ : IsGraphon W₂)
    (hequiv : GEquiv μ₁ W₁ μ₂ W₂) :
    maxCutMix μ₁ W₁ = maxCutMix μ₂ W₂ := by sorry

end GraphonCheeger.Supplement
