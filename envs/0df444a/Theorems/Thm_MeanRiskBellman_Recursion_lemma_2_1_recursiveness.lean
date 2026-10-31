-- Prove2me | Theorems.Thm_MeanRiskBellman_Recursion_lemma_2_1_recursiveness
-- name    : MeanRiskBellman.Recursion.lemma_2_1_recursiveness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:35.816473+00:00
-- url     : https://prove2.me/theorems/dd96ec93-3ab5-41ec-a299-e1fdce401571
-- title:
--   Lemma 2.1, second bullet, p. 6 — time consistency ⇔ recursiveness ρ_t(X) = ρ_t(−ρ_{t+1}(X))
-- statement:
--   Let $(\Omega,\mathcal F,(\mathcal F_t)_{t=0}^T,\mathbb P)$ be a finite filtered probability space with $\mathcal F_0$ trivial, $\mathcal F_T=\mathcal F$ and $\mathbb P(A)>0$ for every nonempty $A\in\mathcal F$, and let $(\rho_t)_{t=0}^T$ be a dynamic convex risk measure ($\rho_t:L_T\to L_t$ normalized, conditionally translation invariant, monotone and conditionally convex). Then $(\rho_t)$ is time consistent if and only if it is **recursive**:
--   $$\rho_t(X)=\rho_t\big(-\rho_{t+1}(X)\big)\qquad\text{for all }X\in L_T\text{ and }0\le t\le T-1 .$$
--
--   Recursiveness is the form of time consistency used in the proofs of Theorem 3.2 and of Lemma B.1 (recursiveness of the mean-risk function $\Gamma_t$).
--
--   **Formalization Note.** Equalities are pointwise; $L_T$ is the set of $\mathcal F$-measurable functions $\Omega\to\mathbb R$.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, p. 6, Lemma 2.1, second bullet

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_DynamicRisk

open MeasureTheory

namespace MeanRiskBellman.Recursion

theorem lemma_2_1_recursiveness {Ω : Type*} [Fintype Ω] [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (T : ℕ) (ℱ : Filtration ℕ mΩ) (ρ : ℕ → (Ω → ℝ) → Ω → ℝ)
    (hP : IsFinFilteredSpace P T ℱ) (hρ : IsDynamicConvexRiskMeasure P T ℱ ρ) :
    TimeConsistent T ρ ↔
      ∀ t < T, ∀ X : Ω → ℝ, Measurable X → ρ t X = ρ t (fun ω => -ρ (t + 1) X ω) := by sorry

end MeanRiskBellman.Recursion
