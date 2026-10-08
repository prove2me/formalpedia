-- Prove2me | Theorems.Thm_GloriaOtto_Variance_lemma_2_7
-- name    : GloriaOtto.Variance.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:13.117816+00:00
-- url     : https://prove2.me/theorems/9e3d51bc-2d6d-4a46-aff7-7b8fc7e3b69b
-- title:
--   Lemma 2.7 — ⟨|φ_T(0)|^n (|∇φ_T(0)|² + |∇*φ_T(0)|²)⟩ ≲ ⟨|φ_T(0)|^n⟩ for even n, uniformly in T
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$. For every even $n \in 2\mathbb N$ there is a constant $C_n$, depending only on $n, d, \alpha, \beta$, such that for every probability law $\nu$ on $\mathbb R$ with $\nu([\alpha,\beta]) = 1$, every $\xi \in \mathbb R^d$ with $|\xi| = 1$ and every $T > 0$, under the i.i.d. law $\nu^{\otimes E}$ of the conductivities,
--   $$\big\langle|\phi_T(0)|^n\big(|\nabla\phi_T(0)|^2 + |\nabla^*\phi_T(0)|^2\big)\big\rangle \le C_n\,\big\langle|\phi_T(0)|^n\big\rangle . \tag{2.17}$$
--
--   This is a Caccioppoli inequality in probability, which relies on the stationarity of $\phi_T$. It provides the gain in stochastic integrability in the proof of Proposition 2.1.
--
--   **Formalization Note.** Both expectations are lower Lebesgue integrals of nonnegative functions in $[0,\infty]$. The constant is chosen before the law $\nu$, $\xi$ and $T$.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Lemma 2.7, (2.17), p. 17

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem lemma_2_7 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∀ n : ℕ, Even n → ∃ C : ℝ, ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      ν (Set.Icc α β)ᶜ = 0 → ∀ ξ : Fin d → ℝ, sqNorm ξ = 1 → ∀ T : ℝ, 0 < T →
        ∫⁻ a, ENNReal.ofReal (|phiT a T ξ 0| ^ n
            * (sqNorm (grad (phiT a T ξ) 0) + sqNorm (gradStar (phiT a T ξ) 0))) ∂(law d ν)
          ≤ ENNReal.ofReal C * ∫⁻ a, ENNReal.ofReal (|phiT a T ξ 0| ^ n) ∂(law d ν) := by sorry

end GloriaOtto.Variance
