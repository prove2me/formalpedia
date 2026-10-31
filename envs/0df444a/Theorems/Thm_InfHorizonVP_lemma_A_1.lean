-- Prove2me | Theorems.Thm_InfHorizonVP_lemma_A_1
-- name    : InfHorizonVP.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:06.732978+00:00
-- url     : https://prove2.me/theorems/7cc269d1-665b-47ff-870a-52e11584e391
-- title:
--   Lemma A.1 — the polar mapping of a measurable closed-valued multifunction
-- statement:
--   Let $E$ be a separable real Banach space and $I\subseteq\mathbb R$ nonempty and closed, with the Lebesgue $\sigma$-algebra $\mathcal L$. Let $\Gamma:I\rightsquigarrow E$ be measurable ($\{t\in I\mid\Gamma(t)\cap O\neq\emptyset\}\in\mathcal L$ for every open $O$) with nonempty closed values. Then the polar mapping $\Gamma^0(t)=\Gamma(t)^0\subseteq E^*$
--
--   1. has its graph $\{(t,x^*)\mid t\in I,\ x^*\in\Gamma^0(t)\}$ in $\mathcal L\otimes\operatorname{Borel}(E^*,w^*)$, and
--   2. admits a weakly$^*$ scalarly measurable selector.
--
--   This is the measurable-selection step in the proof of Theorem A.1, which produces the selector $f$ used to build the adjoint arc of Theorem 4.1.
--
--   **Formalization Note** $\operatorname{Borel}(E^*,w^*)$ is the Borel $\sigma$-algebra of `WeakDual ℝ E`; $\mathcal L$ is the Carathéodory $\sigma$-algebra of Lebesgue outer measure.
--
--   Differences from the source:
--   - encoding: 𝓛 the Lebesgue σ-algebra; E* with the weak* topology → Carathéodory σ-algebra of Lebesgue outer measure (NullMeasurableSet for single sets); WeakDual ℝ E via StrongDual.toWeakDual; reason: Lean convention; the same σ-algebras
--   - encoding: functions and multifunctions on I → on ℝ, with conditions restricted to I; reason: values off I are never used
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, Lemma A.1, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_InfHorizonVP_polarDual
import Definitions.Def_InfHorizonVP_IsWeakStarScalarlyMeasurable
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Lemma A.1 — the polar mapping of a measurable closed-valued multifunction has a measurable
graph and a weak\* scalarly measurable selector.**
Frankowska, Sagara, arXiv:1801.00400v3, Lemma A.1, p.23: "Let E be a separable Banach space. If
Γ : I ⇝ E is a measurable multifunction with nonempty closed values, then its polar mapping
Γ⁰ : I ⇝ E* has the graph in 𝓛 ⊗ Borel(E*, w*) and Γ⁰ admits a weakly* scalarly measurable
selector." Here (p.21) I is "a nonempty closed subset of the real line R with the Lebesgue measure
and the Lebesgue σ-algebra 𝓛", Γ is measurable if (p.23) "the set {t ∈ I | Γ(t) ∩ O ≠ ∅} belongs to
𝓛 for every open subset O of E", and Γ⁰(t) := Γ(t)⁰.

**Formalization Note.** `𝓛` is the Lebesgue σ-algebra, written as the Carathéodory σ-algebra of
Lebesgue outer measure where a σ-algebra on `ℝ` is needed and as `NullMeasurableSet volume` for
single sets (the two agree). `Borel(E*, w*)` is `borel (WeakDual ℝ E)`, and `E*` is identified with
`WeakDual ℝ E` by `StrongDual.toWeakDual`. A selector satisfies `f(t) ∈ Γ⁰(t)` for a.e. `t ∈ I`
(p.21). -/
theorem lemma_A_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (I : Set ℝ) (hI : IsClosed I) (hIne : I.Nonempty) (Γ : ℝ → Set E)
    (hmeas : ∀ O : Set E, IsOpen O → NullMeasurableSet {t | t ∈ I ∧ (Γ t ∩ O).Nonempty} volume)
    (hne : ∀ t ∈ I, (Γ t).Nonempty) (hcl : ∀ t ∈ I, IsClosed (Γ t)) :
    MeasurableSet[MeasurableSpace.prod (volume : Measure ℝ).toOuterMeasure.caratheodory
        (borel (WeakDual ℝ E))]
      {q : ℝ × WeakDual ℝ E | q.1 ∈ I ∧ StrongDual.toWeakDual.symm q.2 ∈ polarDual (Γ q.1)} ∧
    ∃ f : ℝ → E →L[ℝ] ℝ, IsWeakStarScalarlyMeasurable f I ∧
      ∀ᵐ t ∂(volume.restrict I), f t ∈ polarDual (Γ t) := by sorry

end InfHorizonVP
