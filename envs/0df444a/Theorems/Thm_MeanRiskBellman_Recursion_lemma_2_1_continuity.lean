-- Prove2me | Theorems.Thm_MeanRiskBellman_Recursion_lemma_2_1_continuity
-- name    : MeanRiskBellman.Recursion.lemma_2_1_continuity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:31.053994+00:00
-- url     : https://prove2.me/theorems/45daa113-9dcf-4ab7-a3b9-a289f64c13f2
-- title:
--   Lemma 2.1, third bullet, p. 6 — every convex risk measure on a finite probability space is continuous
-- statement:
--   In the setting of the paper (finite filtered probability space with $\mathcal F_0$ trivial, $\mathcal F_T=\mathcal F$ and all nonempty events of positive probability), let $(\rho_t)_{t=0}^T$ be a dynamic convex risk measure. Then every $\rho_t:L_T\to L_t$, $t=0,\dots,T$, is continuous: if $X^n\to X$ in $L_T$ then
--   $$\rho_t(X^n)\longrightarrow\rho_t(X).$$
--
--   This is the continuity used in the proof of Lemma 5.2 (through Lemma B.1) to pass to the limit inside the upper images.
--
--   **Formalization Note.** $L_T$ is the set of $\mathcal F$-measurable functions $\Omega\to\mathbb R$ with the topology of pointwise convergence (on a finite $\Omega$ this is the norm topology); the statement is continuity of $\rho_t$ restricted to this set (`ContinuousOn`). Time consistency is not assumed, as on the page.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, p. 6, Lemma 2.1, third bullet

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_DynamicRisk

open MeasureTheory

namespace MeanRiskBellman.Recursion

theorem lemma_2_1_continuity {Ω : Type*} [Fintype Ω] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : ℕ) (ℱ : Filtration ℕ mΩ) (ρ : ℕ → (Ω → ℝ) → Ω → ℝ)
    (hP : IsFinFilteredSpace P T ℱ) (hρ : IsDynamicConvexRiskMeasure P T ℱ ρ) :
    ∀ t ≤ T, ContinuousOn (ρ t) {X : Ω → ℝ | Measurable X} := by sorry

end MeanRiskBellman.Recursion
