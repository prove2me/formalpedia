-- Prove2me | Theorems.Thm_GloriaOtto_Variance_lemma_2_9
-- name    : GloriaOtto.Variance.lemma_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:17.801442+00:00
-- url     : https://prove2.me/theorems/b9c1f264-0347-4778-b4a0-acdf2d7293ce
-- title:
--   Lemma 2.9 — Meyers-type higher integrability: Σ_{R≤|z|≤2R} |∇_z G_T(z,0)|^q ≲ R^d (R^{1−d})^q min{1, √T/R}^k for some p > 2 and 2 ≤ q ≤ p
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$. There is an exponent $p > 2$, depending only on $d, \alpha, \beta$, with the following property. For all $q \in [2, p]$ and $k > 0$ there are constants $C$ and $R_0$ (depending only on $d, \alpha, \beta, q, k$) such that for every $a \in \mathcal A_{\alpha\beta}$, every $T > 0$ and every $R \ge R_0$,
--   $$\sum_{R\le|z|\le 2R} |\nabla_z G_T(z,0)|^q \le C R^d (R^{1-d})^q \min\{1, \sqrt T R^{-1}\}^k , \tag{2.24}$$
--   where $\nabla_z G_T(z,0) = \big(G_T(z+e_j,0) - G_T(z,0)\big)_{j=1}^d$ is the discrete gradient in the first argument and $|\cdot|$ the Euclidean norm.
--
--   This is the higher integrability of Green's-function gradients (a discrete Meyers estimate), uniform in the coefficients and in $T$. It compensates for the fact that only finite moments of $\nabla\phi_T$ are controlled.
--
--   **Formalization Note.** "$R \gg 1$" is $R \ge R_0$, with $R_0$ chosen after $q$ and $k$ and before $a$ and $T$.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Lemma 2.9, (2.24), p. 19

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem lemma_2_9 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ p : ℝ, 2 < p ∧ ∀ q k : ℝ, 2 ≤ q → q ≤ p → 0 < k → ∃ C R₀ : ℝ,
      ∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T → ∀ R : ℝ, R₀ ≤ R →
        ∑' z, {z : Site d | R ≤ latNorm z ∧ latNorm z ≤ 2 * R}.indicator
            (fun z => (sqNorm (fun j => greenT a T (z + unit j) 0 - greenT a T z 0)) ^ (q / 2)) z
          ≤ C * R ^ (d : ℝ) * (R ^ (1 - (d : ℝ))) ^ q * (min 1 (Real.sqrt T / R)) ^ k := by sorry

end GloriaOtto.Variance
