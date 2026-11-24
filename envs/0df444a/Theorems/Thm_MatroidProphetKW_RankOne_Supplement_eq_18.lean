-- Prove2me | Theorems.Thm_MatroidProphetKW_RankOne_Supplement_eq_18
-- name    : MatroidProphetKW.RankOne.Supplement.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:05:54.642551+00:00
-- url     : https://prove2.me/theorems/9fa34aed-e404-4282-b3d8-ed09f3aa602c
-- title:
--   (18), p. 14 (corrected: adversary key V(A∪{x}, i)) — R(M) ≥ R(M^copies)
-- statement:
--   Consider a BMUMD instance with services $\mathcal U$ partitioned into the groups $J_1,\dots,J_n$ of bidders $1,\dots,n$. The values $v_x$ are independent, and each has a density positive on its support interval, a regular distribution (monotone virtual valuation $\varphi_x$). Let the feasibility constraint be either
--
--   1. a matroid $\mathcal M$ on $\mathcal U$, with the thresholds $T(A,x)=\tfrac12\,\mathbb E[w'(R(A))-w'(R(A\cup\{x\}))]$ of (9), or
--   2. the intersection of $p\ge1$ matroids $\mathcal M_1,\dots,\mathcal M_p$, with the thresholds $T(A,x)=\sum_j\tfrac1{2p}\,\mathbb E[w'(R_j(A))-w'(R_j(A\cup\{x\}))]$ of §4.2.
--
--   In both cases the constraint is unit-demand: no feasible set contains two services of one group. The ghost weights $w'$ are drawn from the laws of the clipped virtual values $\max(\varphi_x(v_x),0)$. Let $M$ be the posted-price mechanism of Algorithm 1 and $M^{\mathrm{copies}}$ the mechanism of Algorithm 3, run in the order chosen by the adversary of Algorithm 2. Then
--   $$R(M)\ \ge\ R(M^{\mathrm{copies}}).$$
--
--   This is the first of the two steps of the chain (16) that the paper proves itself. It shows that the adversary of Algorithm 2 is a worst case for $M^{\mathrm{copies}}$, so $M$, which processes the bidders in their fixed order, earns at least as much.
--
--   **Formalization Note** Both clauses are one conjunction; no finite-mean premise on the values is added. Each mechanism has only finitely many possible finite prices, so its payments are bounded and integrable even for unbounded value laws.
--
--   Differences from the source:
--
--   - correction: Algorithm 2, line 17 (p. 13) sorts J_i by p_x + V(A ∪ {x}, i − 1) → the adversary sorts J_i by p_x + V(A ∪ {x}, i); reason: V(A, i) is the revenue from J_{i+1}, …, J_n after J_i, as in preprocessing line 7 ("Sort J_{i+1} in order of increasing p_x + V(A ∪ {x}, i + 1)") and in the proof of (18) on p. 15 (min{p_x + V(A ∪ {x}, i + 1) | x ∈ K} for J_{i+1}); the printed index points to a table entry of the wrong stage (V(·, n − 1) instead of V(·, n) = 0 for the last group); no case is excluded
--   - reading: the thresholds come from the prophet algorithm run on the weights φ_x(v_x), which may be negative, while the algorithms of §§2–4 take non-negative weights → T(A, x) is computed from the laws of max(φ_x(v_x), 0); reason: §2 takes non-negative weights, and downward closure permits discarding negative virtual values without changing the offline maximum; prices still use the original virtual-value inverse, so negative virtual values are rejected even at threshold zero; no equality with the clipped run at that tie is asserted
--   - reading: φ_x^{-1} is not defined when φ_x is not invertible → φ_x^{-1}(t) = inf{v ∈ I_x : φ_x(v) ≥ t}, and +∞ when that set is empty; reason: generalized inverse of a monotone function, equal to the inverse where φ_x is strictly increasing and continuous
--   - reading: "bidder i chooses an element x ∈ J_i (or nothing) at these posted prices" → bidder i buys a utility-maximizing service among those with b_x ≥ p_x, ties broken by a fixed enumeration, and buys nothing iff there is none; reason: the choice of a utility-maximizing bidder; the tie events are null under densities
--   - reading: M^copies takes T(A, x) from the prophet algorithm run on the adversary's order → thresholds at the set M^copies has allocated so far; reason: the source uses A for its selected services; the local recursion preserves its inverse-price test and advances this actual allocation, including rejection of negative virtual values at threshold zero; the source proof's equality with the online allocation is interpreted using the original virtual-value test, up to null generalized-inverse boundary events
--   - encoding: bidders 1, …, n and ties in the adversary's sort are unspecified → bidders Fin n (0-based), ties broken by the fixed enumeration Fintype.equivFin; reason: Lean convention; the sort key is unchanged
--   - encoding: F_x(p) in (17), with infinite prices allowed → F_x(p) = Pr[v_x ≤ p] and F_x(∞) = 1; reason: equals Pr[v_x < p], the probability of not buying, because the laws have densities
--   - encoding: "the intersection of p matroids" → 0 < p; reason: excludes only p = 0, for which no matroid is given and 4p − 2 < 0
--   - reading: Algorithm 2 preprocessing lists stages n through 1, while the proof of (18) uses V(∅,0) → V is defined by (17) also at stage 0, with V(A,n)=0; reason: the definition of V(A,i) as revenue from the remaining groups and the induction on PDF page 16 include i=0; this supplies an omitted table boundary, without changing any ordering or allocation
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 14, (18); proof pp. 14–15 (PDF 15–16); Algorithms 1–3 and (17), pp. 12–14

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Algorithm
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_RankOne_Supplement_ValueDist
import Definitions.Def_MatroidProphetKW_RankOne_Supplement_Mechanisms

open MeasureTheory

namespace MatroidProphetKW.RankOne.Supplement

/-- (18) (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 14, proved on p. 15): in a BMUMD setting with
independent regular valuations, the expected revenue of mechanism `M`
(Algorithm 1) is at least that of `M^copies` (Algorithm 3, with the adversary of Algorithm 2):
`R(M) ≥ R(M^copies)`. First clause: a matroid constraint with the thresholds (9) of §3.3; second
clause: the intersection of `p ≥ 1` matroids with the thresholds of §4.2 at `α = 2p`. The
thresholds are computed from the laws of the clipped virtual values `max(φ_x(v_x), 0)`. -/
theorem eq_18 {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (owner : α → Fin n)
    (D : α → ValueDist) (hreg : ∀ x, (D x).Regular) :
    (∀ M : Matroid α, M.E = Set.univ → IsUnitDemand (fun S => M.Indep (↑S : Set α)) owner →
      copiesRevenue D (fun S => M.Indep (↑S : Set α))
          (MatroidProphetKW.Single.kwT M (fun x => (D x).wLaw)) owner ≤
        (mechM D (fun S => M.Indep (↑S : Set α))
          (MatroidProphetKW.Single.kwT M (fun x => (D x).wLaw)) owner).revenue D) ∧
    (∀ (p : ℕ) (M : Fin p → Matroid α), 0 < p → (∀ j, (M j).E = Set.univ) →
      IsUnitDemand (MatroidProphetKW.Inter.IsIndep M) owner →
      copiesRevenue D (MatroidProphetKW.Inter.IsIndep M)
          (MatroidProphetKW.Inter.Tsum M (fun x => (D x).wLaw) (2 * p)) owner ≤
        (mechM D (MatroidProphetKW.Inter.IsIndep M)
          (MatroidProphetKW.Inter.Tsum M (fun x => (D x).wLaw) (2 * p)) owner).revenue D) := by sorry

end MatroidProphetKW.RankOne.Supplement
