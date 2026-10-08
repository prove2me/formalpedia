-- Prove2me | Theorems.Thm_GloriaOtto_Variance_lemma_2_2_pathwise
-- name    : GloriaOtto.Variance.lemma_2_2_pathwise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:14.361728+00:00
-- url     : https://prove2.me/theorems/c18a9a49-d3b8-4c74-9a50-2162dd528981
-- title:
--   Lemma 2.2 (pathwise) — (2.3) has a unique bounded solution φ_T for every a ∈ A_αβ, and T⁻¹⟨φ_T²⟩ + ⟨|∇φ_T|²⟩ ≲ |ξ|²
-- statement:
--   Let $d \ge 2$ and $0 < \alpha \le \beta$.
--
--   1. For every conductivity function $a \in \mathcal A_{\alpha\beta}$, every $T > 0$ and every $\xi \in \mathbb R^d$, the approximate corrector equation
--   $$T^{-1}u(x) - \nabla^*\cdot A(x)\big(\nabla u(x) + \xi\big) = 0 \qquad (x \in \mathbb Z^d) \tag{2.3}$$
--   has exactly one bounded solution $u : \mathbb Z^d \to \mathbb R$; it is denoted $\phi_T(\cdot\,; a)$.
--   2. There is a constant $C$, depending only on $d$, $\alpha$, $\beta$, such that for every probability law $\nu$ on $\mathbb R$ with $\nu([\alpha,\beta]) = 1$, every $T > 0$ and every $\xi \in \mathbb R^d$, under the i.i.d. law $\nu^{\otimes E}$ of the conductivities,
--   $$T^{-1}\langle\phi_T(0)^2\rangle + \langle|\nabla\phi_T(0)|^2\rangle \le C|\xi|^2 .$$
--
--   Part 1 is the pathwise core of Lemma 2.2: the paper's stationary, mean-zero $\phi_T$ is obtained from this bounded solution (see the definitions file). Part 2 is the lemma's energy estimate, written at the origin, which is legitimate by stationarity.
--
--   **Formalization Note.** The expectation is a lower Lebesgue integral of a nonnegative function, so it cannot vanish by a non-integrability default.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Lemma 2.2, (2.3), p. 10

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem lemma_2_2_pathwise (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    (∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T → ∀ ξ : Fin d → ℝ,
      ∃! u : Site d → ℝ, IsApproxCorrector a T ξ u) ∧
    ∃ C : ℝ, ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ν (Set.Icc α β)ᶜ = 0 →
      ∀ T : ℝ, 0 < T → ∀ ξ : Fin d → ℝ,
        ∫⁻ a, ENNReal.ofReal (T⁻¹ * phiT a T ξ 0 ^ 2 + sqNorm (grad (phiT a T ξ) 0)) ∂(law d ν)
          ≤ ENNReal.ofReal (C * sqNorm ξ) := by sorry

end GloriaOtto.Variance
