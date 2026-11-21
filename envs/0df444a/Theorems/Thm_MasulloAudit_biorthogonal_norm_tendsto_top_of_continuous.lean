-- Prove2me | Theorems.Thm_MasulloAudit_biorthogonal_norm_tendsto_top_of_continuous
-- name    : MasulloAudit.biorthogonal_norm_tendsto_top_of_continuous
-- status  : Proved
-- author  : @lll
-- created : 2026-11-21T00:32:17.704571+00:00
-- url     : https://prove2.me/theorems/3d8cc206-c831-41b4-84d9-2eb41b26c273
-- title:
--   Functionals separating nearby vectors of a continuous family blow up: $\|f_s\|\to\infty$
-- statement:
--   Let $E$ be a normed space over $\mathbb K\in\{\mathbb R,\mathbb C\}$, let $\eta:\mathbf R\to E$ be continuous at $t$, and for each $s\ne t$ let $f_s\in E'$ be a continuous linear functional with $f_s(\eta_t)=1$ and $f_s(\eta_s)=0$. Then
--
--   $$
--   \|f_s\|\longrightarrow\infty\qquad(s\to t,\ s\ne t).
--   $$
--
--   Indeed $\|f_s\|\ge1/\|\eta_t-\eta_s\|$, and the denominator tends to $0$.
--
--   In Chapter 10 of Masullo's draft the vectors $\eta_\rho$ attached to zeta zeros (with the same character, real part and $m$) depend continuously on the ordinate. In the relevant weighted norms, $\|\eta_t-\eta_s\|$ depends only on $t-s$. Consecutive zeros have gaps tending to $0$, so the bound $\|f_s\|\ge1/\|\eta_t-\eta_s\|$, applied to consecutive zeros, shows that the biorthogonal functionals $\psi_\rho$ cannot be uniformly bounded. That bound is used in the proofs of Theorems 10.3.1.1 (p. 451, after (10.3.1.18)) and 10.4.2.8 ((10.4.2.24), p. 463), and is based on the invalid inference in Terminology 10.2.1.2(2) (p. 444). The companion theorem `MasulloAudit.exp_family_weighted_dist_tendsto_zero` supplies the continuity of $t\mapsto\eta_t$ for the exponential family in weighted $L^2$.
--
--   **Formalization Note.** No injectivity of $\eta$ is assumed: $\eta_s\ne\eta_t$ follows from the two conditions on $f_s$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf; Terminology 10.2.1.2(2) (p. 444), proof of Thm 10.3.1.1 (p. 451), (10.4.2.24) (p. 463), Prop. 10.2.2.2 (pp. 446-447)

import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

namespace MasulloAudit

/-- If `η` is continuous at `t` and `f s` are continuous linear functionals with
`f s (η t) = 1` and `f s (η s) = 0` for `s ≠ t`, then `‖f s‖ → ∞` as `s → t`, `s ≠ t`. -/
theorem biorthogonal_norm_tendsto_top_of_continuous {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (η : ℝ → E) (t : ℝ) (hη : ContinuousAt η t) (f : ℝ → E →L[𝕜] 𝕜)
    (h₁ : ∀ s, s ≠ t → f s (η t) = 1) (h₀ : ∀ s, s ≠ t → f s (η s) = 0) :
    Tendsto (fun s => ‖f s‖) (𝓝[≠] t) atTop := by sorry

end MasulloAudit
