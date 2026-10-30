-- Prove2me | Theorems.Thm_GenCostSched_GFCS_beta_increment_le
-- name    : GenCostSched.GFCS.beta_increment_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:37.642669+00:00
-- url     : https://prove2.me/theorems/f437cd12-c933-4803-a2fe-a74299ce51c1
-- title:
--   Proof of Theorem 3, p. 22 — by monotone substitution and (26), ∫_{r_n}^∞ (β̂′_t − β̂_t) dt ≤ K Δ_n(Alg)
-- statement:
--   At the arrival of job $n$ at $s=r_n$, let $A$ be the alive old jobs (released no later than $s$, positive lengths $\rho_j$), and let job $n$ have $r_n=s$ and length $v_n$. Assume the standing assumptions of §II and twice differentiability. Let $K\ge 1$ satisfy $(t-r_\ell)g''_\ell(t)\le(K-1)g'_\ell(t)$ for all $\ell$ and $t\ge r_\ell$. Let $x$ be an optimal integral schedule of $\mathrm{RNF}(r_n)$ (jobs $A$) and $x'$ one of $\mathrm{RNF}'(r_n)$ (jobs $A\cup\{n\}$). Assume that $x'$ postpones $x$ on the old jobs, as the monotone substitute property provides: for each $\ell\in A$ and $u\ge s$, $x'$ has processed at most as much of $\ell$ by time $u$ as $x$. Write $\hat\beta,\hat\beta'$ for the bounds (20) of $x$ and $x'$, and
--   $$\Delta_n(\mathrm{Alg})=\mathrm{cost}(x')-\mathrm{cost}(x)=\mathrm{RNF}'(r_n)-\mathrm{RNF}(r_n)$$
--   (Definition 4). Then
--   $$\int_{r_n}^\infty\big(\hat\beta'_t-\hat\beta_t\big)\,dt\;\le\;K\,\Delta_n(\mathrm{Alg}).$$
--
--   This is the step of Theorem 3's proof where monotone substitution and the curvature constant $K$ enter. Combined with (22), it gives $\Delta_n(\mathrm{Alg})\le\frac{1+\epsilon}{1+\epsilon-K}\Delta_s(D)$.
--
--   **Formalization Note.** Costs are finite for integral schedules, which finish in finite time, so they enter as real numbers (`toReal`).
--
--   Differences from the source:
--
--   - reading: 'by monotone substitute property, adding a new job can only postpone the processing intervals of the alive jobs' → the hypothesis postpones s A x x′ (cumulative-processing dominance) on the two optimal integral schedules; reason: the reading of Definition 5 used throughout; the statement isolates the step of the proof that uses it
--   - generalization: K = 1 + sup_{ℓ, t ≥ r_ℓ} (t − r_ℓ) g″_ℓ(t)/g′_ℓ(t) → any real K with K ≥ 1 and (t − r_ℓ) g″_ℓ(t) ≤ (K − 1) g′_ℓ(t) for all ℓ and t ≥ r_ℓ (CurvBound K); reason: when g′ > 0 and the supremum is finite, the paper's K satisfies CurvBound and is the least such K, so the statement specializes to the paper's; the multiplicative form avoids division by g′ = 0 and an sSup of an unbounded set
--   - generalization: the instance RNF(r_n)/RNF′(r_n) met by Algorithm 2 at the arrival of job n (alive jobs A(r_n), residual lengths) → every identical-release instance GFCS(s) of jobs A with r_j ≤ s and positive lengths ρ_j, plus a new job k with r_k = s and length v_k; reason: every arrival of Algorithm 2 is such an instance (A = A(r_n), ρ = residual lengths), so the statement specializes to the paper's
--   - encoding: Δ_n(Alg) = RNF′(r_n) − RNF(r_n) → cost(x′) − cost(x) with x, x′ the optimal integral schedules, as real numbers; reason: optimal integral schedules attain RNF and RNF′; their costs are finite
--   - encoding: β̂_t = Σ_ℓ Σ_d [g_ℓ(C_ℓ^{2d}) − g_ℓ(C_ℓ^{2d−1})] over the processing intervals after t → β̂_t = Σ_ℓ ∫_{(t,∞)} g′_ℓ(τ) x_ℓ(τ) dτ (betaHat); reason: equal by the fundamental theorem of calculus on each interval, as in (23), p. 21; the integral form is defined for every measurable schedule
--   - encoding: the derivative g′_j of g_j on [r_j, ∞) → a given function g' j tied to g j by HasDerivWithinAt (g j) (g' j t) (Ici (r j)) t for t ≥ r_j (JobStanding); reason: g_j is defined and differentiable only on [r_j, ∞) (p. 5), so its derivative there is the within-derivative; supplying it as data changes no instance
--   - encoding: g″_ℓ in K (Theorem 3), so g_ℓ twice differentiable on [r_ℓ, ∞) → a given function g'' ℓ with HasDerivWithinAt (g' ℓ) (g'' ℓ t) (Ici (r ℓ)) t for t ≥ r_ℓ (TwiceDiff); reason: K is defined through g″, so the theorem presupposes it on [r_ℓ, ∞); supplying it as data changes no instance
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, p. 22, proof of Theorem 3, (24)–(26) and the paragraph after (26)

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-- The bound derived from (26) (proof of Theorem 3, p. 22): when the new job `k` arrives at
`s = r_k` and the new optimal integral schedule `x′` postpones the old one `x` on the alive
jobs, `∫_s^∞ (β̂′_t − β̂_t) dt ≤ K Δ`, with `Δ = cost(x′) − cost(x) = RNF′ − RNF`. -/
theorem beta_increment_le {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j)
    (h2 : I.TwiceDiff) (K : ℝ) (hK : I.CurvBound K) (s : ℝ) (A : Finset (Fin m))
    (ρ : Fin m → ℝ) (k : Fin m) (hk : k ∉ A) (hA : ∀ j ∈ A, I.r j ≤ s) (hrk : I.r k = s)
    (hρ : ∀ j ∈ A, 0 < ρ j) (hρk : ρ k = I.v k) (x x' : Fin m → ℝ → ℝ)
    (hx : IsOptIntegral I.g s A ρ x) (hx' : IsOptIntegral I.g s (insert k A) ρ x')
    (hpost : postpones s A x x') :
    ∫ t in Ici s, (betaHat I.g' x' t - betaHat I.g' x t) ≤
      K * ((offCost I.g x').toReal - (offCost I.g x).toReal) := by sorry

end GenCostSched.GFCS
