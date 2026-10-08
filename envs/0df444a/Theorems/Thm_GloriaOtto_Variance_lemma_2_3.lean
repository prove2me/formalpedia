-- Prove2me | Theorems.Thm_GloriaOtto_Variance_lemma_2_3
-- name    : GloriaOtto.Variance.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:09.076033+00:00
-- url     : https://prove2.me/theorems/bfbddcf0-8966-4e57-ab4b-96cdb2aec558
-- title:
--   Lemma 2.3 — var[X] ≤ ⟨Σ_i sup_{a_i} |∂X/∂a_i|²⟩ var[a₁] for a function of i.i.d. variables with range [α, β]
-- statement:
--   Let $0 < \alpha \le \beta$ and let $\nu$ be a probability measure on $\mathbb R$ with $\nu([\alpha,\beta]) = 1$. Let $a = (a_i)_{i\in\mathbb N}$ be i.i.d. with law $\nu$, i.e. distributed according to the product measure $P = \nu^{\otimes\mathbb N}$ on $\mathbb R^{\mathbb N}$. Let $X : \mathbb R^{\mathbb N} \to \mathbb R$ be measurable for the product $\sigma$-algebra, and assume that for every $a \in [\alpha,\beta]^{\mathbb N}$ and every $i$ the map $s \mapsto X(a_1,\dots,a_{i-1}, s, a_{i+1},\dots)$ is differentiable on $[\alpha,\beta]$. Then
--   $$\operatorname{var}[X] \le \Big\langle \sum_{i=1}^{\infty}\sup_{a_i\in[\alpha,\beta]}\Big|\frac{\partial X}{\partial a_i}\Big|^2\Big\rangle\,\operatorname{var}[a_1]. \tag{2.7}$$
--
--   This is the variance estimate through which every bound of the paper is obtained: it reduces a variance to the sensitivity of $X$ to each single coefficient. Unlike the spectral-gap inequality, it holds for atomic laws.
--
--   **Formalization Note.** Coordinates are indexed from $0$ in Lean. Variances, the series and the expectation are taken in $[0,\infty]$, so (2.7) is not made trivial by non-integrability defaults. The derivative is the derivative within $[\alpha,\beta]$, one-sided at the endpoints, and the supremum runs over $a_i \in [\alpha,\beta]$. The differentiability hypothesis is implicit in the paper's use of $\partial X/\partial a_i$.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Lemma 2.3, (2.7), p. 14

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem lemma_2_3 (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc α β)ᶜ = 0)
    (X : (ℕ → ℝ) → ℝ) (hX : Measurable X)
    (hdiff : ∀ a : ℕ → ℝ, (∀ j, a j ∈ Set.Icc α β) → ∀ i : ℕ,
      DifferentiableOn ℝ (fun s => X (Function.update a i s)) (Set.Icc α β)) :
    evariance X (Measure.infinitePi (fun _ : ℕ => ν))
      ≤ (∫⁻ a, ∑' i : ℕ,
          (⨆ t ∈ Set.Icc α β,
            ‖derivWithin (fun s => X (Function.update a i s)) (Set.Icc α β) t‖ₑ) ^ 2
          ∂(Measure.infinitePi (fun _ : ℕ => ν))) * evariance id ν := by sorry

end GloriaOtto.Variance
