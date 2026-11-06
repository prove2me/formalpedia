-- Prove2me | Theorems.Thm_NondualOpt_lemma_18
-- name    : NondualOpt.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:30.739806+00:00
-- url     : https://prove2.me/theorems/c29aa133-8d03-4948-995e-ff7a3c31fd0f
-- title:
--   Lemma 18 — one-dimensional capped domination
-- statement:
--   Let $T\ge1$, let $Q_1,\dots,Q_T$ be probability measures on $[-1,1]$ with means $m_t=\int z\,dQ_t(z)$, let $z_1,\dots,z_T\in[-1,1]$ and $\bar m=\frac1T\sum_tm_t$. Then
--   $$
--   \bar m-\max_{\lambda\in\Delta_T^{(2)}}\sum_{t=1}^T\lambda_tz_t\le\sup_{\phi\in\Phi}\Big[\frac1T\sum_{t=1}^T\int\phi\,dQ_t-\frac2T\sum_{t=1}^T\phi(z_t)\Big].
--   $$
--   No coupling between the $Q_t$ and the points $z_t$ is assumed. Applied to pushforwards along a realized path, it yields Lemma 5.
--
--   Differences from the source:
--   - encoding: max over Δ_T^{(2)} and sup over Φ → real suprema over the two sets as types; reason: both sets are nonempty (uniform weights; φ = 0) and both families are bounded above (by 1 and by 2), so these are the true maximum and supremum
--   - encoding: Q_1, …, Q_T and the factor 2/T → T ≥ 1, rounds Fin T; reason: the statement presupposes at least one measure
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Lemma 18, p.26

import Mathlib
import Definitions.Def_NondualOpt_cappedSimplex
import Definitions.Def_NondualOpt_PhiClass

open MeasureTheory

namespace NondualOpt

/-- **Lemma 18 (One-dimensional capped domination).** Let `Q_1, …, Q_T` be probability measures on
`[−1, 1]` with means `m_t`, `z_1, …, z_T ∈ [−1, 1]`, and `m̄ = (1/T)∑_t m_t`. Then
`m̄ − max_{λ ∈ Δ_T^{(2)}} ∑_t λ_t z_t ≤ sup_{ϕ ∈ Φ} [(1/T)∑_t ∫ ϕ dQ_t − (2/T)∑_t ϕ(z_t)]`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Lemma 18, p.26.

**Formalization Note.** `T ≥ 1`. The maximum over the capped simplex and the supremum over `Φ` are
real `⨆` over subtypes; both index sets are nonempty (uniform weights; `ϕ = 0`) and both families
are bounded above (by `1` and by `2`), so these are the true maximum and supremum. -/
theorem lemma_18 (T : ℕ) (hT : 1 ≤ T) (Q : Fin T → ProbabilityMeasure (Set.Icc (-1 : ℝ) 1))
    (z : Fin T → Set.Icc (-1 : ℝ) 1) :
    (1 / T : ℝ) * ∑ t, ∫ x, (x : ℝ) ∂(Q t : Measure (Set.Icc (-1 : ℝ) 1)) -
        ⨆ w : cappedSimplex T 2, ∑ t, (w : Fin T → ℝ) t * (z t : ℝ) ≤
      ⨆ ϕ : PhiClass, ((1 / T : ℝ) * ∑ t, ∫ x, (ϕ : Set.Icc (-1 : ℝ) 1 → ℝ) x
          ∂(Q t : Measure (Set.Icc (-1 : ℝ) 1)) -
        (2 / T : ℝ) * ∑ t, (ϕ : Set.Icc (-1 : ℝ) 1 → ℝ) (z t)) := by sorry

end NondualOpt
