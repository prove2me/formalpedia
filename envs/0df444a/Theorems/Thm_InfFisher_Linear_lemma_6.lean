-- Prove2me | Theorems.Thm_InfFisher_Linear_lemma_6
-- name    : InfFisher.Linear.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:46.350947+00:00
-- url     : https://prove2.me/theorems/921c15e0-6f54-4518-b38b-97508be30fec
-- title:
--   Lemma 6, p. 15 — continuum second welfare theorem
-- statement:
--   Let $\Theta\subseteq\mathbb R^d$ be compact. Each buyer $i$ has a nonnegative integrable valuation $v_i$ with $\int_\Theta v_i>0$. If $x$ is a Pareto optimal feasible allocation, then there are budgets $B_i\ge0$ and an integrable nonnegative price $p$ for which $(x,p)$ is a Fisher market equilibrium:
--
--   $$\exists B\in\mathbb R_+^n,\;\exists p,\qquad (x,p)\text{ is a market equilibrium for }(v,B).$$
--
--   The utility $\langle v_i,x_i\rangle$ is therefore buyer $i$'s equilibrium utility. This continuum version of the second welfare theorem supports the interval utility characterization.
--
--   **Formalization Note** Valuations and allocations are functions on Euclidean space with Lebesgue measure restricted to $\Theta$. Budgets may be zero, as the paper states.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Lemma 6, p. 15

import Mathlib
import Definitions.Def_InfFisher_Linear_Setting

namespace InfFisher.Linear

open MeasureTheory

/-- Gao–Kroer, Lemma 6: a second welfare theorem for a continuum of items. -/
theorem lemma_6 {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (x : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hx : InfFisher.EG.IsParetoOptimal (volume.restrict Θ) v x) :
    ∃ B : Fin n → ℝ, (∀ i, 0 ≤ B i) ∧
      ∃ p, IsME (volume.restrict Θ) v B x p := by sorry

end InfFisher.Linear
