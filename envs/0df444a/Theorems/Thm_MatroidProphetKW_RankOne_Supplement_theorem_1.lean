-- Prove2me | Theorems.Thm_MatroidProphetKW_RankOne_Supplement_theorem_1
-- name    : MatroidProphetKW.RankOne.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:07:14.38941+00:00
-- url     : https://prove2.me/theorems/a79dd927-7824-43c7-8000-0e023e30dfd0
-- title:
--   Theorem 1 (corrected: vanishing revenue tails) — M is truthful and IR and 2-approximates matroid revenue / (4p − 2)-approximates p-matroid revenue
-- statement:
--   Consider a Bayesian multi-parameter unit-demand (BMUMD) instance. The services $\mathcal U$ are partitioned into the groups $J_1,\dots,J_n$ of bidders $1,\dots,n$. The values $v_x$ are independent; each has a density positive on its support interval, a regular distribution (monotone virtual valuation $\varphi_x$) and a vanishing upper revenue tail: $\lim_{z\to\infty}z\Pr[v_x>z]=0$. Finite means imply this condition, but are not required. Let $M$ be the posted-price mechanism of Algorithm 1, with prices $p_x=\varphi_x^{-1}(T(A,x))$, or $\infty$ when $A\cup\{x\}$ is infeasible. The thresholds are computed from the laws of $\max(\varphi_x(v_x),0)$.
--
--   1. **Matroid constraints.** Let the feasible sets be the independent sets of a matroid on $\mathcal U$ that meet each $J_i$ in at most one service, and let $T$ be the thresholds (9) of §3.3. Then $M$ is an individually rational and truthful deterministic mechanism, and for every individually rational and truthful deterministic mechanism $\mathcal A$ for the instance
--   $$R(\mathcal A)\ \le\ 2\,R(M).$$
--   2. **Matroid intersections.** Let the feasible sets be the common independent sets of $p\ge1$ matroids on $\mathcal U$, again meeting each $J_i$ in at most one service, and let $T$ be the §4.2 thresholds with $\alpha=2p$. Then $M$ is an individually rational and truthful deterministic mechanism, and for every individually rational and truthful deterministic mechanism $\mathcal A$
--   $$R(\mathcal A)\ \le\ (4p-2)\,R(M).$$
--
--   $R(\cdot)$ is the expected revenue under truthful bids. Truthful means dominant-strategy incentive compatible over each bidder's whole report for $J_i$. Individually rational means a served bidder pays at most its value and an unserved bidder pays nothing. Payments are measurable and integrable.
--
--   The corrected theorem turns the matroid prophet inequality into a sequential posted-price mechanism for unit-demand bidders. Its approximation ratios match the prophet inequality's.
--
--   **Formalization Note** The vanishing-tail premise is an explicit correction, not a standing assumption stated in §6. The printed guarantee fails for an equal-revenue value law: one bidder with two rank-one services, X with tail Pr[X > v] = 3/v on [3, ∞), and independent Y uniform on [1, 2], has virtual values 0 and 2Y − 2. Mechanism M uses threshold 1/2, never offers X at a finite price, and earns 15/16 from Y, whereas posting price 3 for X earns 3 > 2(15/16). The added premise excludes this nonzero tail boundary (equal to 3 for X). It retains every finite-mean law and also infinite-mean laws with z·Pr[v_x > z] → 0. Both feasibility clauses and both constants are retained, without bounding the support. "The optimal deterministic mechanism" is the benchmark class of Lemma 4: the inequality is stated against every member of that class, so no optimal mechanism needs to exist.
--
--   Differences from the source:
--
--   - reading: "a 2-approximation to the revenue of the optimal deterministic mechanism" → R(A) ≤ 2·R(M) (resp. (4p − 2)·R(M)) for every individually rational, dominant-strategy truthful deterministic mechanism A with feasible allocations and measurable, integrable payments; reason: the class of Lemma 4 (from Chawla et al. [5]), through which the proof bounds R(OPT); a supremum over the class need not be attained
--   - generalization: the theorem asserts only the revenue guarantee → the Lean also asserts that M itself is individually rational and truthful; reason: the first paragraph of the proof claims it ("Both M and M^copies are posted-price (hence, truthful) mechanisms that always output a feasible allocation"); dropping the conjunct gives the corrected revenue guarantee; the printed domain separately requires the explicit tail repair
--   - correction: Theorem 1 and §6 omit an upper-tail boundary condition on values → for every service x, z Pr[v_x > z] tends to 0 as z tends to +∞; reason: the printed claim fails for the independent regular equal-revenue/uniform instance in the Formalization Note and DISPROOF.md (R(M) = 15/16, R(A) = 3); integration of φf = vf − (1−F) gives the boundary term z(1−F(z)) in the revenue/virtual-surplus identity used by (16); the added premise removes that term; excluded cases are laws with nonvanishing or nonconvergent upper revenue tail, including the counterexample with limit 3; all finite-mean laws and also infinite-mean laws with vanishing revenue tail remain allowed
--   - reading: the thresholds come from the prophet algorithm run on the weights φ_x(v_x), which may be negative, while the algorithms of §§2–4 take non-negative weights → T(A, x) is computed from the laws of max(φ_x(v_x), 0); reason: §2 takes non-negative weights, and downward closure permits discarding negative virtual values without changing the offline maximum; prices still use the original virtual-value inverse, so negative virtual values are rejected even at threshold zero; no equality with the clipped run at that tie is asserted
--   - reading: φ_x^{-1} is not defined when φ_x is not invertible → φ_x^{-1}(t) = inf{v ∈ I_x : φ_x(v) ≥ t}, and +∞ when that set is empty; reason: generalized inverse of a monotone function, equal to the inverse where φ_x is strictly increasing and continuous
--   - reading: "bidder i chooses an element x ∈ J_i (or nothing) at these posted prices" → bidder i buys a utility-maximizing service among those with b_x ≥ p_x, ties broken by a fixed enumeration, and buys nothing iff there is none; reason: the choice of a utility-maximizing bidder; the tie events are null under densities
--   - encoding: bidders 1, …, n → bidders Fin n (0-based), processed in increasing order; reason: Lean convention
--   - encoding: "the intersection of p matroids" → 0 < p; reason: excludes only p = 0, for which no matroid is given and 4p − 2 < 0
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 14, Theorem 1; §6 pp. 11–14 (BMUMD, Lemma 4, regularity, Algorithm 1, (16))

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Algorithm
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_RankOne_Supplement_ValueDist
import Definitions.Def_MatroidProphetKW_RankOne_Supplement_Mechanisms

open MeasureTheory

namespace MatroidProphetKW.RankOne.Supplement

/-- Corrected Theorem 1 (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 14): for BMUMD settings with independent
regular valuations with vanishing upper revenue tail, mechanism `M` (Algorithm 1) is an individually rational,
truthful deterministic mechanism whose expected revenue is at least `1/2` (matroid feasibility
constraint, thresholds (9) of §3.3) resp. `1/(4p − 2)` (intersection of `p ≥ 1` matroids,
thresholds of §4.2 at `α = 2p`) of the expected revenue of every individually rational and
truthful deterministic mechanism for the instance.
The upper-tail premise is an explicit repair: §6 omits the boundary condition
`v * Pr[value > v] → 0`, and the printed claim fails for an equal-revenue tail
(see the supplement DISPROOF.md). Finite means imply this condition; they are not required.
Both approximation factors and both feasibility classes are retained, on possibly unbounded supports. -/
theorem theorem_1 {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (owner : α → Fin n)
    (D : α → ValueDist) (hreg : ∀ x, (D x).Regular)
    (htail : ∀ x, Filter.Tendsto (fun v : ℝ => v * (D x).law.real (Set.Ioi v))
      Filter.atTop (nhds 0)) :
    (∀ M : Matroid α, M.E = Set.univ → IsUnitDemand (fun S => M.Indep (↑S : Set α)) owner →
      IsTruthfulIR D (fun S => M.Indep (↑S : Set α)) owner
          (mechM D (fun S => M.Indep (↑S : Set α))
            (MatroidProphetKW.Single.kwT M (fun x => (D x).wLaw)) owner) ∧
      ∀ A : BMech α n, IsTruthfulIR D (fun S => M.Indep (↑S : Set α)) owner A →
        A.revenue D ≤ 2 * (mechM D (fun S => M.Indep (↑S : Set α))
          (MatroidProphetKW.Single.kwT M (fun x => (D x).wLaw)) owner).revenue D) ∧
    (∀ (p : ℕ) (M : Fin p → Matroid α), 0 < p → (∀ j, (M j).E = Set.univ) →
      IsUnitDemand (MatroidProphetKW.Inter.IsIndep M) owner →
      IsTruthfulIR D (MatroidProphetKW.Inter.IsIndep M) owner
          (mechM D (MatroidProphetKW.Inter.IsIndep M)
            (MatroidProphetKW.Inter.Tsum M (fun x => (D x).wLaw) (2 * p)) owner) ∧
      ∀ A : BMech α n, IsTruthfulIR D (MatroidProphetKW.Inter.IsIndep M) owner A →
        A.revenue D ≤ (4 * (p : ℝ) - 2) * (mechM D (MatroidProphetKW.Inter.IsIndep M)
          (MatroidProphetKW.Inter.Tsum M (fun x => (D x).wLaw) (2 * p)) owner).revenue D) := by sorry

end MatroidProphetKW.RankOne.Supplement
