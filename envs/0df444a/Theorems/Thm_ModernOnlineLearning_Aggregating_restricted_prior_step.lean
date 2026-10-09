-- Prove2me | Theorems.Thm_ModernOnlineLearning_Aggregating_restricted_prior_step
-- name    : ModernOnlineLearning.Aggregating.restricted_prior_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:02.180704+00:00
-- url     : https://prove2.me/theorems/06d5d370-ab38-49ad-a336-0eb0e241e191
-- title:
--   Proof of Theorem 11.5, p. 183 — exp-concave losses on the shrunken competitor set
-- statement:
--   Let $d,T\geq1$, $\alpha>0$, $V\subseteq\mathbb R^d$ be convex, $u\in V$, and each $\ell_t$ be $\alpha$-exp-concave on $V$. Put $r=(T/d)/(T/d+1)$ and $V'=\{ru+(1-r)w:w\in V\}$. For every $x\in V'$ there is $w\in V$ with $x=ru+(1-r)w$, and for $1\leq t\leq T$,
--
--   $$e^{-\alpha\ell_t(x)}\geq r e^{-\alpha\ell_t(u)}+(1-r)e^{-\alpha\ell_t(w)}\geq r e^{-\alpha\ell_t(u)}.$$
--
--   Consequently,
--
--   $$e^{-\alpha\sum_{t=1}^T\ell_t(x)}\geq r^T e^{-\alpha\sum_{t=1}^T\ell_t(u)}\geq e^{-d}e^{-\alpha\sum_{t=1}^T\ell_t(u)}.$$
--
--   This gives the loss comparison on the portion of the prior retained near a fixed competitor.
--
--   **Formalization Note** The hypotheses $d,T\geq1$ make the scaling and the printed division by $d$ well defined.
-- source:
--   Orabona, arXiv:1912.13213v10, proof of Theorem 11.5, p. 183, first two display chains

import Mathlib
import Definitions.Def_ModernOnlineLearning_Aggregating_ExpConcave
import Definitions.Def_ModernOnlineLearning_Aggregating_ShrunkSet
set_option autoImplicit false

namespace ModernOnlineLearning.Aggregating

/-- The two exponential inequalities in the proof of Theorem 11.5, p. 183. -/
theorem restricted_prior_step {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 0 < T)
    (V : Set (EuclideanSpace ℝ (Fin d))) (hV : Convex ℝ V)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V)
    (α : ℝ) (hα : 0 < α)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓ : ∀ t ∈ Finset.Icc 1 T, ExpConcaveOn V α (ℓ t)) :
    ∀ x ∈ shrunkSet V u T, ∃ w ∈ V,
      x = (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) • u +
          (1 / ((T : ℝ) / (d : ℝ) + 1)) • w ∧
      (∀ t ∈ Finset.Icc 1 T,
        Real.exp (-α * ℓ t x) ≥
          (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) *
            Real.exp (-α * ℓ t u) +
          (1 / ((T : ℝ) / (d : ℝ) + 1)) * Real.exp (-α * ℓ t w) ∧
        (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) *
            Real.exp (-α * ℓ t u) +
          (1 / ((T : ℝ) / (d : ℝ) + 1)) * Real.exp (-α * ℓ t w) ≥
          (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) *
            Real.exp (-α * ℓ t u)) ∧
      Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t x) ≥
        ((((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) ^ T) *
        Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) ∧
      Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t x) ≥
        Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) / Real.exp (d : ℝ) := by sorry

end ModernOnlineLearning.Aggregating
