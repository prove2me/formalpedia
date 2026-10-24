-- Prove2me | Theorems.Thm_GenCostSched_GFCS_speed_tradeoff
-- name    : GenCostSched.GFCS.speed_tradeoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:50.27502+00:00
-- url     : https://prove2.me/theorems/625731c9-3eb8-4940-bdad-10776db90ee0
-- title:
--   Proof of Theorem 3, p. 22 — for 1 + ε > K, Algorithm 2 is (1+ε)-speed (1+ε)/(1+ε−K)-competitive for GFCS
-- statement:
--   Let an online GFCS instance satisfy the standing assumptions of §II, with cost functions twice differentiable on $[r_j,\infty)$ and belonging to a monotone substitute class $H$ (Definition 5). Let $K\ge 1$ satisfy $(t-r_\ell)g''_\ell(t)\le(K-1)g'_\ell(t)$ for all $\ell$ and $t\ge r_\ell$. Then for every run of Algorithm 2 and every $\epsilon$ with $1+\epsilon>K$,
--   $$\mathrm{Cost(Alg)}\;\le\;\frac{1+\epsilon}{1+\epsilon-K}\;\mathrm{OPT}_{1/(1+\epsilon)},$$
--   where $\mathrm{OPT}_{1/(1+\epsilon)}$ is the optimal value of the slower LP (21), i.e. of LP (1) on a machine of speed $1/(1+\epsilon)$. Thus Algorithm 2 is $(1+\epsilon)$-speed $\frac{1+\epsilon}{1+\epsilon-K}$-competitive.
--
--   Theorem 3 is the case $1+\epsilon=2K$. Smaller speed-ups give larger ratios. For concave costs, $K=1$, the bound is $(1+\epsilon)$-speed $\frac{1+\epsilon}{\epsilon}$-competitive (Example 3).
--
--   **Formalization Note.** $\mathrm{Cost(Alg)}$ and $\mathrm{OPT}$ are valued in $[0,\infty]$, and the ratio enters through `ENNReal.ofReal`.
--
--   Differences from the source:
--
--   - generalization: K = 1 + sup_{ℓ, t ≥ r_ℓ} (t − r_ℓ) g″_ℓ(t)/g′_ℓ(t) → any real K with K ≥ 1 and (t − r_ℓ) g″_ℓ(t) ≤ (K − 1) g′_ℓ(t) for all ℓ and t ≥ r_ℓ (CurvBound K); reason: when g′ > 0 and the supremum is finite, the paper's K satisfies CurvBound and is the least such K, so the statement specializes to the paper's; the multiplicative form avoids division by g′ = 0 and an sSup of an unbounded set
--   - reading: Definition 5: adding a new job to the offline identical-release instance can only postpone the optimal scheduling intervals of the existing jobs; H = {g_ℓ(t) : g_ℓ(0) = 0} → IsMonotoneSubstitute H: for every identical-release instance GFCS(s) with cost functions in H (nonnegative, nondecreasing on [s, ∞)) and positive lengths, every optimal integral schedule x, and every new job, some optimal integral schedule x′ of the enlarged instance has, for each old job and each u ≥ s, processed at most as much of it by time u as x; H is any set containing every g_j, the normalization being g_j(r_j) = 0; reason: the definition fixes neither which optimal schedules are compared nor what postponing means; cumulative-processing dominance is the property the proof uses (p. 22) and is implied by the literal reading (each interval moved to the right), so the hypothesis is no stronger than the literal one
--   - reading: Algorithm 2: let x^o(t) denote the optimal solution of GFCS(r_n) and follow it from r_n on → a run (IsAlg2Run) re-solves at each arrival with an optimal integral schedule (optimal among fractional schedules) that postpones the continuing schedule on the old alive jobs; reason: the algorithm does not say which optimal solution is taken when there are several; the proof (p. 22) needs the postponing one, which exists by the monotone substitute property
--   - encoding: (1+ε)-speed (1+ε)/(1+ε−K)-competitive against the slower dual optimum Cost(D_s) and weak duality → Cost(Alg) ≤ ofReal((1+ε)/(1+ε−K)) · OPT_LP(1/(1+ε)); reason: the normalization of (21): online capacity 1 against the LP benchmark with capacity 1/(1+ε)
--   - encoding: cost functions g_j and fractional cost Σ_j ∫ (v_j(t)/v_j) g′_j(t) dt → the data g_j are the scaled functions g_j/v_j of p. 6 and the cost is Σ_j ∫ g_j(t) x_j(t) dt; reason: the paper's own redefinition after the integration by parts on p. 6; the two descriptions are in bijection and K is unchanged by the scaling
--   - encoding: real-valued LP objectives and optimal values → costs, OPT_c and RNF are lintegrals in ℝ≥0∞ of ENNReal.ofReal of the integrand; reason: the integrand g_j(t) x_j(t) is nonnegative on every schedule (x_j vanishes before r_j, where g_j ≥ 0), so nothing changes, and no non-integrable schedule can get the junk cost 0
--   - encoding: jobs j = 1, 2, … arriving online with r_1 ≤ r_2 ≤ … (p. 18) → finitely many jobs Fin n with Monotone r; jobs with equal release times are processed one after another in index order; reason: the analysis is over a finite instance (proof of Lemma 5); ties are allowed by r_1 ≤ r_2 ≤ …
--   - encoding: the derivative g′_j of g_j on [r_j, ∞) → a given function g' j tied to g j by HasDerivWithinAt (g j) (g' j t) (Ici (r j)) t for t ≥ r_j (JobStanding); reason: g_j is defined and differentiable only on [r_j, ∞) (p. 5), so its derivative there is the within-derivative; supplying it as data changes no instance
--   - encoding: g″_ℓ in K (Theorem 3), so g_ℓ twice differentiable on [r_ℓ, ∞) → a given function g'' ℓ with HasDerivWithinAt (g' ℓ) (g'' ℓ t) (Ici (r ℓ)) t for t ≥ r_ℓ (TwiceDiff); reason: K is defined through g″, so the theorem presupposes it on [r_ℓ, ∞); supplying it as data changes no instance
-- source:
--   Etesami, An Optimal Control Framework for Online Job Scheduling with General Cost Functions, arXiv:1906.02644v3, p. 22, proof of Theorem 3 ('…we get Cost(Alg) ≤ (1+ϵ)/(1+ϵ−K) Cost(Ds) … Using weak duality …')

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GenCostSched.GFCS

/-- Speed trade-off (proof of Theorem 3, p. 22): for a monotone substitute class and every
`ε` with `1 + ε > K`, Algorithm 2 is `(1+ε)`-speed `(1+ε)/(1+ε−K)`-competitive:
`Cost(Alg) ≤ (1+ε)/(1+ε−K) · OPT_{1/(1+ε)}`. -/
theorem speed_tradeoff {n : ℕ} (I : Instance n) (H : Set (ℝ → ℝ)) (K : ℝ) (hI : I.Standing)
    (h2 : I.TwiceDiff) (hH : ∀ j, I.g j ∈ H) (hMS : IsMonotoneSubstitute H)
    (hK : I.CurvBound K) (X : ℕ → Fin n → ℝ → ℝ) (hX : I.IsAlg2Run X) (ε : ℝ)
    (hε : K < 1 + ε) :
    I.algCost X ≤ ENNReal.ofReal ((1 + ε) / (1 + ε - K)) * I.optLP (1 / (1 + ε)) := by sorry

end GenCostSched.GFCS
