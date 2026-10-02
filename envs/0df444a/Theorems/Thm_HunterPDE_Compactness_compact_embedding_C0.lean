-- Prove2me | Theorems.Thm_HunterPDE_Compactness_compact_embedding_C0
-- name    : HunterPDE.Compactness.compact_embedding_C0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:34:43.501988+00:00
-- url     : https://prove2.me/theorems/e999c377-a7a5-4bef-8277-4217a100513c
-- title:
--   Theorem 3.48 — for p > n, uniform Lᵖ gradient bounds with support in Ω give precompactness in C₀(ℝⁿ)
-- statement:
--   Let $\Omega$ be a bounded open set in $\mathbb{R}^n$, and $n < p < \infty$. Suppose that $\mathcal{F}$ is a set of functions whose weak derivative belongs to $L^p(\mathbb{R}^n)$ such that: (a) $\operatorname{supp} f \Subset \Omega$; (b) there exists a constant $C$ such that
--   $$\|Df\|_{L^p} \le C \qquad \text{for all } f \in \mathcal{F}.$$
--   Then $\mathcal{F}$ is precompact in $C_0(\mathbb{R}^n)$.
--
--   This is the supercritical companion of the Rellich–Kondrachov theorem. Above the dimension, gradient bounds give uniform bounds and equicontinuity, so the compactness is in the uniform norm.
--
--   **Formalization Note.** Each $f : \mathbb{R}^n \to \mathbb{R}$ is locally integrable, with weak first partials $\partial_i f \in L^p(\mathbb{R}^n)$. $\operatorname{supp} f \Subset \Omega$ means that $f$ vanishes a.e. outside some compact $K \subseteq \Omega$. $\|Df\|_{L^p}$ is the $L^p$ norm of the Euclidean length of the weak gradient, and $C$ is uniform over $\mathcal{F}$. The conclusion states that every $f$ has a representative in Mathlib's `C₀(ℝⁿ, ℝ)` (a continuous representative is unique), and that the set of these representatives has compact closure in the sup norm. $n \ge 1$ is assumed, as the book's $\mathbb{R}^n$ always has it; the statement is false on $\mathbb{R}^0$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 75, Theorem 3.48

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv

open MeasureTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace HunterPDE.Compactness

/-- Theorem 3.48 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 75: let `Ω` be a bounded open
set in `ℝⁿ` and `n < p < ∞`. Suppose that `F` is a set of functions whose weak derivative belongs
to `Lᵖ(ℝⁿ)` such that (a) `supp f ⋐ Ω`; (b) there is a constant `C` with `‖Df‖_{Lᵖ} ≤ C` for all
`f ∈ F`. Then `F` is precompact in `C₀(ℝⁿ)`.
Each `f` is locally integrable on `ℝⁿ` with weak first partials `∂ᵢf ∈ Lᵖ(ℝⁿ)`; `supp f ⋐ Ω`
is: `f` vanishes a.e. outside a compact `K ⊆ Ω`; `‖Df‖_{Lᵖ}` is the `Lᵖ` norm of the Euclidean
length of the weak gradient. The conclusion says every `f` has a representative in `C₀(ℝⁿ)`
(continuous, vanishing at infinity; unique since continuous functions equal a.e. are equal), and
the set of these representatives has compact closure in the sup norm. `1 ≤ n` is the book's
standing `ℝⁿ` (the statement is false on `ℝ⁰`). -/
theorem compact_embedding_C0 {n : ℕ} (hn : 1 ≤ n) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (p : ℝ) (hnp : (n : ℝ) < p)
    (F : Set (EuclideanSpace ℝ (Fin n) → ℝ))
    (hFD : ∀ f ∈ F, ∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      Shared.HasWeakDeriv Set.univ (Pi.single i 1) f g ∧ MemLp g (ENNReal.ofReal p) volume)
    (hFsupp : ∀ f ∈ F, ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ K ⊆ Ω ∧
      ∀ᵐ x ∂volume, x ∉ K → f x = 0)
    (hFb : ∃ C : ℝ≥0, ∀ f ∈ F,
      eLpNorm (Shared.weakGradNorm Set.univ f) (ENNReal.ofReal p) volume ≤ (C : ℝ≥0∞)) :
    (∀ f ∈ F, ∃ u : C₀(EuclideanSpace ℝ (Fin n), ℝ), (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] f) ∧
      IsCompact (closure {u : C₀(EuclideanSpace ℝ (Fin n), ℝ) |
        ∃ f ∈ F, (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] f}) := by sorry

end HunterPDE.Compactness
