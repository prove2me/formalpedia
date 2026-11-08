-- Prove2me | Theorems.Thm_GraphonCheeger_lemma_4_29
-- name    : GraphonCheeger.lemma_4_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:58:27.581424+00:00
-- url     : https://prove2.me/theorems/3f5df6fd-b2c4-437c-aaa7-7b5f8f746637
-- title:
--   Lemma 4.29: membership in $\mathcal W_c$ is invariant under equivalence of graphons
-- statement:
--   Let $W_1$ and $W_2$ be graphons, possibly on different probability spaces $(\Omega_1,\mu_1)$ and $(\Omega_2,\mu_2)$, and let $c\in[0,1]$. If $W_1\cong W_2$, that is $\delta_\square(W_1,W_2)=0$, then
--
--   $$W_1\in\mathcal W_c\iff W_2\in\mathcal W_c .$$
--
--   So $\mathcal W_c$ is a well-defined set of graph limits.
--
--   Differences from the source:
--   - encoding: $W_1\cong W_2$ (equivalence of graphons, Definition 2.6, by homomorphism densities) → $\delta_\square(W_1,W_2)=0$; reason: the paper records the equivalence $\delta_\square(W_1,W_2)=0\iff W_1\cong W_2$ as (A.7), p.81, and the mission does not define homomorphism densities.
--   - encoding: the infimum in $\delta_\square$ over all probability spaces → over probability spaces in the universe `Type (max u v)` of the two graphons' spaces; reason: every common space pushes forward to a coupling on $\Omega_1\times\Omega_2$, which lies in that universe and has no larger cut norm, so the value is the same.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Lemma 4.29, pp.48–49; (A.7), p.81

import Mathlib
import Definitions.Def_GraphonCheeger_cutDist
import Definitions.Def_GraphonCheeger_InWc

open MeasureTheory

namespace GraphonCheeger

/-- Lemma 4.29, pp.48–49 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W₁, W₂` be graphons, possibly on different probability
spaces, and `c ∈ [0, 1]`. If `W₁ ≅ W₂`, then `W₁ ∈ W_c ⇔ W₂ ∈ W_c`.

**Formalization Note.** Equivalence `W₁ ≅ W₂` is stated as `δ_□(W₁, W₂) = 0`, which the paper
records as equivalent to it ((A.7), p.81). -/
theorem lemma_4_29 {Ω₁ : Type*} {Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
    (W₁ : Ω₁ → Ω₁ → ℝ) (W₂ : Ω₂ → Ω₂ → ℝ) (hW₁ : IsGraphon W₁) (hW₂ : IsGraphon W₂)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (hequiv : cutDist μ₁ W₁ μ₂ W₂ = 0) :
    InWc μ₁ W₁ c ↔ InWc μ₂ W₂ c := by sorry

end GraphonCheeger
