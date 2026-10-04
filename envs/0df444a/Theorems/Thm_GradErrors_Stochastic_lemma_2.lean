-- Prove2me | Theorems.Thm_GradErrors_Stochastic_lemma_2
-- name    : GradErrors.Stochastic.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:18:06.953288+00:00
-- url     : https://prove2.me/theorems/f509d3d7-44d5-43e7-99c0-30575a76c20b
-- title:
--   Lemma 2, p. 637 — if E[r_t | 𝓕_t] = 0 and E[‖r_t‖² | 𝓕_t] ≤ B, then Σ γ_t r_t and Σ γ_t²‖r_t‖² converge a.s. when Σ γ_t² < ∞
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $\mathcal F_0\subseteq\mathcal F_1\subseteq\cdots\subseteq\mathcal F$, let $V$ be a finite-dimensional real inner-product space (for instance $\mathbb R$ or $\mathbb R^n$), and let $(\gamma_t)_{t\ge0}$ be deterministic real numbers with
--   $$\sum_{t=0}^\infty\gamma_t^2<\infty .$$
--   Let $r_t:\Omega\to V$ be random vectors such that, for every $t$,
--
--   1. $r_t$ is $\mathcal F_{t+1}$-measurable;
--   2. $\|r_t\|^2$ is integrable;
--   3. $E[r_t\mid\mathcal F_t]=0$ almost surely;
--   4. $E[\|r_t\|^2\mid\mathcal F_t]\le B$ almost surely, where $B$ is a deterministic constant.
--
--   Then, with probability 1, both sequences of partial sums
--   $$\sum_{t=0}^{T}\gamma_t r_t\qquad\text{and}\qquad\sum_{t=0}^{T}\gamma_t^2\|r_t\|^2,\qquad T=0,1,\dots,$$
--   converge to finite limits as $T\to\infty$.
--
--   In the proof of Proposition 3 this lemma is applied to the noise $w_t$ rescaled by $\mathcal F_t$-measurable factors (Lemma 3 of the paper), to show that the accumulated noise and its second-order contribution are almost surely finite.
--
--   **Formalization Note** The space is a general finite-dimensional real inner-product space, because the paper applies the lemma both to real-valued and to $\mathbb R^n$-valued $r_t$. The conditional expectations are Mathlib's `condExp`. Integrability of $\|r_t\|^2$ is stated explicitly: Mathlib's conditional expectation of a non-integrable function is $0$, so without it hypotheses 3 and 4 would hold vacuously. It costs nothing, since $E[\|r_t\|^2\mid\mathcal F_t]\le B$ in the paper's sense already gives $E\|r_t\|^2\le B$. Convergence is convergence of the partial sums, not Lean's `Summable`, which would mean unconditional convergence; $\sum_t\gamma_tr_t$ may converge only conditionally. Only $\sum_t\gamma_t^2<\infty$ is assumed of the stepsizes, as in the paper.
-- source:
--   Bertsekas and Tsitsiklis, Gradient Convergence in Gradient Methods with Errors, SIAM J. Optim. 10 (2000), https://doi.org/10.1137/S1052623497331063, p. 637, Lemma 2

import Mathlib

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace

namespace GradErrors.Stochastic

theorem lemma_2 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (γ : ℕ → ℝ) (hsq : Summable (fun t => γ t ^ 2))
    (r : ℕ → Ω → F) (B : ℝ)
    (hrm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (r t))
    (hr2 : ∀ t, Integrable (fun ω => ‖r t ω‖ ^ 2) P)
    (hr0 : ∀ t, P[r t | ℱ t] =ᵐ[P] 0)
    (hrB : ∀ t, P[fun ω => ‖r t ω‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => B) :
    ∀ᵐ ω ∂P,
      (∃ S : F, Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), γ t • r t ω) atTop (𝓝 S)) ∧
      (∃ S' : ℝ,
        Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), γ t ^ 2 * ‖r t ω‖ ^ 2) atTop (𝓝 S')) := by sorry

end GradErrors.Stochastic
