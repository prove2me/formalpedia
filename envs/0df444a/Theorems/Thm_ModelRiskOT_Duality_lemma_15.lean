-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_lemma_15
-- name    : ModelRiskOT.Duality.lemma_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:54:25.666623+00:00
-- url     : https://prove2.me/theorems/a074532d-03e4-4459-8a2a-0ac9a6c68cee
-- title:
--   Lemma 15 — a signed measure with a negative part has dual value $-\infty$
-- statement:
--   Let $S$ be a compact Polish space (so $S\times S$ is a compact Polish space) and $f:S\to\mathbb R$ upper semicontinuous. Let $\pi$ be a finite signed Borel measure on $S\times S$ with Jordan decomposition $\pi=\pi^+-\pi^-$, and suppose $\pi^+(A)=0<\pi^-(A)$ for some Borel set $A\subseteq S\times S$. Then
--
--   $$\inf\Big\{\int g\,d\pi : g\in C_b(S\times S),\ g(x,y)\ge f(y)\text{ for all }x,y\Big\}=-\infty.$$
--
--   In the proof of Proposition 5 this identifies the domain of the conjugate functional in Fenchel duality as nonnegative measures.
--
--   **Formalization Note** $\int g\,d\pi$ is written $\int g\,d\pi^+-\int g\,d\pi^-$ and "$\inf=-\infty$" as: for every real $M$ some bounded continuous $g$ with $g(x,y)\ge f(y)$ has $\int g\,d\pi<M$. The page's "$\pi^-(A)<\infty$" is automatic for a finite signed measure and is not stated.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 42, Appendix B.3, Lemma 15

import Mathlib

open MeasureTheory BoundedContinuousFunction

namespace ModelRiskOT.Duality

/-- **Lemma 15** (Blanchet & Murthy, arXiv:1604.01446v2, App. B.3, p. 42). Let `S` be a compact
Polish space (so `S × S` is a compact Polish space) and `f : S → ℝ` upper semicontinuous. Let
`π` be a finite signed measure on `S × S` with Jordan decomposition `π = π⁺ − π⁻` such that
`π⁺(A) = 0 < π⁻(A)` for some Borel `A`. Then
`inf {∫ g dπ : g ∈ C_b(S × S), g(x, y) ≥ f(y)} = −∞`, i.e. for every real `M` some bounded
continuous `g ≥ f(y)` has `∫ g dπ⁺ − ∫ g dπ⁻ < M`. -/
theorem lemma_15 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S] [CompactSpace S]
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f)
    (π : SignedMeasure (S × S)) (A : Set (S × S)) (hA : MeasurableSet A)
    (hpos : π.toJordanDecomposition.posPart A = 0)
    (hneg : 0 < π.toJordanDecomposition.negPart A) :
    ∀ M : ℝ, ∃ g : S × S →ᵇ ℝ, (∀ x y, f y ≤ g (x, y)) ∧
      (∫ p, g p ∂π.toJordanDecomposition.posPart) - (∫ p, g p ∂π.toJordanDecomposition.negPart)
        < M := by sorry

end ModelRiskOT.Duality
