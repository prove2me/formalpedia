-- Prove2me | Theorems.Thm_GenCostSched_GFCS_theorem_3
-- name    : GenCostSched.GFCS.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:41.738406+00:00
-- url     : https://prove2.me/theorems/682f957d-ad28-4d6d-87ad-204175b0e99a
-- title:
--   Theorem 3, p. 20 — for a monotone substitute class of cost functions, Algorithm 2 is 2K-speed 2-competitive for GFCS
-- statement:
--   Consider the online single-machine problem GFCS of §II. Jobs $j=1,\dots,n$ arrive at times $0\le r_1\le\cdots\le r_n$ with lengths $v_j>0$ and cost functions $g_j$ (scaled by $1/v_j$, p. 6). On $[r_j,\infty)$ each $g_j$ is nonnegative, nondecreasing and twice differentiable, with $g_j(r_j)=0$. Suppose the cost functions belong to a *monotone substitute* class $H$ (Definition 5): adding a new job to an offline instance with identical release times can only postpone the optimal processing of the existing jobs. Let
--   $$K\;\ge\;1+\sup_{\ell,\ t\ge r_\ell}\frac{(t-r_\ell)\,g''_\ell(t)}{g'_\ell(t)},$$
--   or, more generally, any $K\ge 1$ with $(t-r_\ell)g''_\ell(t)\le (K-1)g'_\ell(t)$ for all $\ell$ and $t\ge r_\ell$. Then Algorithm 2, which re-solves the offline problem at every arrival and follows an optimal integral schedule, is $2K$-speed $2$-competitive. For every run,
--   $$\mathrm{Cost(Alg)}\;=\;\sum_j\int_{r_j}^\infty g_j(t)\,x_j(t)\,dt\;\le\;2\,\mathrm{OPT}_{1/(2K)},$$
--   where $\mathrm{OPT}_{1/(2K)}$ is the optimal value of the LP relaxation (1) on a machine of speed $1/(2K)$, i.e. LP (21) with $1+\epsilon=2K$.
--
--   This is the main result of §IV, and to the author's knowledge the first speed-augmented competitive algorithm for general nondecreasing cost functions on a single machine. Combined with the black-box reduction of Lemma 1, it gives a guarantee for the integral objective $\sum_jg_j(C_j)$.
--
--   **Formalization Note.** A run of Algorithm 2 is a sequence of schedules $X_0=0,\dots,X_n$. At the arrival of job $k$ the schedule is kept before $r_k$, and from $r_k$ on it is replaced by an optimal integral schedule of the alive jobs and job $k$ with their residual lengths. That schedule is optimal among all fractional schedules, and it postpones the continuing schedule on the old jobs. Costs and OPT are valued in $[0,\infty]$.
--
--   Differences from the source:
--
--   - generalization: K = 1 + sup_{ℓ, t ≥ r_ℓ} (t − r_ℓ) g″_ℓ(t)/g′_ℓ(t) → any real K with K ≥ 1 and (t − r_ℓ) g″_ℓ(t) ≤ (K − 1) g′_ℓ(t) for all ℓ and t ≥ r_ℓ (CurvBound K); reason: when g′ > 0 and the supremum is finite, the paper's K satisfies CurvBound and is the least such K, so the statement specializes to the paper's; the multiplicative form avoids division by g′ = 0 and an sSup of an unbounded set
--   - reading: Definition 5: adding a new job to the offline identical-release instance can only postpone the optimal scheduling intervals of the existing jobs; H = {g_ℓ(t) : g_ℓ(0) = 0} → IsMonotoneSubstitute H: for every identical-release instance GFCS(s) with cost functions in H (nonnegative, nondecreasing on [s, ∞)) and positive lengths, every optimal integral schedule x, and every new job, some optimal integral schedule x′ of the enlarged instance has, for each old job and each u ≥ s, processed at most as much of it by time u as x; H is any set containing every g_j, the normalization being g_j(r_j) = 0; reason: the definition fixes neither which optimal schedules are compared nor what postponing means; cumulative-processing dominance is the property the proof uses (p. 22) and is implied by the literal reading (each interval moved to the right), so the hypothesis is no stronger than the literal one
--   - reading: Algorithm 2: let x^o(t) denote the optimal solution of GFCS(r_n) and follow it from r_n on → a run (IsAlg2Run) re-solves at each arrival with an optimal integral schedule (optimal among fractional schedules) that postpones the continuing schedule on the old alive jobs; reason: the algorithm does not say which optimal solution is taken when there are several; the proof (p. 22) needs the postponing one, which exists by the monotone substitute property
--   - encoding: 2K-speed 2-competitive (Definition 1): the online machine is 2K times faster than the optimal offline one, and the benchmark is the optimal offline LP cost (1) (p. 7) → the online machine has capacity 1 and Cost(Alg) ≤ 2 · OPT_LP(1/(2K)), the value of LP (1) with capacity 1/(2K), i.e. LP (21) with 1 + ε = 2K; reason: this is the normalization the proof itself uses (p. 21, (21)); only the ratio of the speeds matters
--   - encoding: cost functions g_j and fractional cost Σ_j ∫ (v_j(t)/v_j) g′_j(t) dt → the data g_j are the scaled functions g_j/v_j of p. 6 and the cost is Σ_j ∫ g_j(t) x_j(t) dt; reason: the paper's own redefinition after the integration by parts on p. 6; the two descriptions are in bijection and K is unchanged by the scaling
--   - encoding: real-valued LP objectives and optimal values → costs, OPT_c and RNF are lintegrals in ℝ≥0∞ of ENNReal.ofReal of the integrand; reason: the integrand g_j(t) x_j(t) is nonnegative on every schedule (x_j vanishes before r_j, where g_j ≥ 0), so nothing changes, and no non-integrable schedule can get the junk cost 0
--   - encoding: jobs j = 1, 2, … arriving online with r_1 ≤ r_2 ≤ … (p. 18) → finitely many jobs Fin n with Monotone r; jobs with equal release times are processed one after another in index order; reason: the analysis is over a finite instance (proof of Lemma 5); ties are allowed by r_1 ≤ r_2 ≤ …
--   - encoding: the derivative g′_j of g_j on [r_j, ∞) → a given function g' j tied to g j by HasDerivWithinAt (g j) (g' j t) (Ici (r j)) t for t ≥ r_j (JobStanding); reason: g_j is defined and differentiable only on [r_j, ∞) (p. 5), so its derivative there is the within-derivative; supplying it as data changes no instance
--   - encoding: g″_ℓ in K (Theorem 3), so g_ℓ twice differentiable on [r_ℓ, ∞) → a given function g'' ℓ with HasDerivWithinAt (g' ℓ) (g'' ℓ t) (Ici (r ℓ)) t for t ≥ r_ℓ (TwiceDiff); reason: K is defined through g″, so the theorem presupposes it on [r_ℓ, ∞); supplying it as data changes no instance
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, p. 20, Theorem 3 (proof pp. 20–22)

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-- Theorem 3 (p. 20): for a monotone substitute class of cost functions, Algorithm 2 is
`2K`-speed `2`-competitive for GFCS, where `K` bounds the curvature
`1 + sup_{ℓ, t ≥ r_ℓ} (t − r_ℓ) g″_ℓ(t)/g′_ℓ(t)`: the cost of every run is at most twice the
optimal value of LP (1) on a machine of speed `1/(2K)` (LP (21) with `1 + ε = 2K`). -/
theorem theorem_3 {n : ℕ} (I : Instance n) (H : Set (ℝ → ℝ)) (K : ℝ) (hI : I.Standing)
    (h2 : I.TwiceDiff) (hH : ∀ j, I.g j ∈ H) (hMS : IsMonotoneSubstitute H)
    (hK : I.CurvBound K) (X : ℕ → Fin n → ℝ → ℝ) (hX : I.IsAlg2Run X) :
    I.algCost X ≤ 2 * I.optLP (1 / (2 * K)) := by sorry

end GenCostSched.GFCS
