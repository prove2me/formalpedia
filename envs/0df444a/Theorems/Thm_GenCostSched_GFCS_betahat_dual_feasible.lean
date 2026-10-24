-- Prove2me | Theorems.Thm_GenCostSched_GFCS_betahat_dual_feasible
-- name    : GenCostSched.GFCS.betahat_dual_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:43.677689+00:00
-- url     : https://prove2.me/theorems/7e19960f-1055-4d0f-8af2-74c6f8543600
-- title:
--   Proof of Theorem 3, pp. 20–21 — replacing each new tail β′ by its upper bound β̂′ in the dual update of Algorithm 2 keeps the dual (2) feasible
-- statement:
--   Let $X_0=0,X_1,\dots,X_n$ be a run of Algorithm 2, and let the dual update choose, at each arrival $k$, an optimal dual $(\alpha^{(k)},\beta^{(k)})$ of $\mathrm{RNF}'(r_k)$, as in Lemma 5. Keep the α-variables $\alpha_k=\alpha^{(k)}_k$. Replace each new tail $\beta^{(k)}$ by the upper bound $\hat\beta'$ of (20) computed from the new schedule $X_{k+1}$:
--   $$\beta_t=\hat\beta^{(k)}_t=\sum_\ell\int_{(t,\infty)}g'_\ell(\tau)\,X_{k+1,\ell}(\tau)\,d\tau\quad\text{for } r_k\le t<r_{k+1},\qquad \beta_t=0\ \text{ for }t<r_1 .$$
--   The resulting dual solution is still feasible for the dual program (2).
--
--   In the proof of Theorem 3 this is the dual whose objective, measured in the slower dual (21), is compared with the cost of the algorithm.
--
--   **Formalization Note.** Dual variables are per unit length, and feasibility holds for almost every $t$.
--
--   Differences from the source:
--
--   - reading: the dual update of Algorithm 2 with the tails β′ replaced by β̂′ while keeping the α-variables as before → for each arrival k any optimal dual (A k, B k) of RNF′(r_k) fixes a_k = A k k; β = β̂ of X_{k+1} on [r_k, next release), 0 before r_1; reason: the α-choice is that of Lemma 5, which the passage invokes
--   - encoding: β̂_t = Σ_ℓ Σ_d [g_ℓ(C_ℓ^{2d}) − g_ℓ(C_ℓ^{2d−1})] over the processing intervals after t → β̂_t = Σ_ℓ ∫_{(t,∞)} g′_ℓ(τ) x_ℓ(τ) dτ (betaHat); reason: equal by the fundamental theorem of calculus on each interval, as in (23), p. 21; the integral form is defined for every measurable schedule
--   - encoding: jobs j = 1, 2, … arriving online with r_1 ≤ r_2 ≤ … (p. 18) → finitely many jobs Fin n with Monotone r; jobs with equal release times are processed one after another in index order; reason: the analysis is over a finite instance (proof of Lemma 5); ties are allowed by r_1 ≤ r_2 ≤ …
--   - encoding: dual (2): α_j/v_j ≤ β_t + g_j(t) for all t ≥ r_j, α_j, β_t ≥ 0 → per-unit variables a_j = α_j/v_j (residual length for GFCS(s)); β integrable on the horizon; β ≥ 0 and the constraints hold for almost every t; reason: β is a density on the time axis: changing it on a null set changes no dual objective; the pointwise form would make optimal duals ill-defined
--   - encoding: the derivative g′_j of g_j on [r_j, ∞) → a given function g' j tied to g j by HasDerivWithinAt (g j) (g' j t) (Ici (r j)) t for t ≥ r_j (JobStanding); reason: g_j is defined and differentiable only on [r_j, ∞) (p. 5), so its derivative there is the within-derivative; supplying it as data changes no instance
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, pp. 20–21, proof of Theorem 3 ('Next, we note that setting the β-dual variable higher …')

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-- β̂-feasibility (proof of Theorem 3, pp. 20–21): in the dual update of Algorithm 2, replacing
each new tail `B k` by the upper bound `β̂′` of the new schedule `X (k+1)`, while keeping the
α-variables `a_k = A k k`, still gives a feasible solution of the dual (2). -/
theorem betahat_dual_feasible {n : ℕ} (I : Instance n) (hI : I.Standing)
    (X : ℕ → Fin n → ℝ → ℝ) (hX : I.IsAlg2Run X) (A : Fin n → Fin n → ℝ) (B : Fin n → ℝ → ℝ)
    (hAB : ∀ k : Fin n, IsOffOptDual I.g (I.r k) (insert k (I.aliveOld (X k.val) k))
      (I.residual (X k.val) k) (A k) (B k)) :
    I.IsDualFeas (fun k => A k k)
      (I.concatDual (fun k => betaHat I.g' (X (k.val + 1)))) := by sorry

end GenCostSched.GFCS
