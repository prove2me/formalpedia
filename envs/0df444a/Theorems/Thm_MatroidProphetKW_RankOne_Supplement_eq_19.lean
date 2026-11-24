-- Prove2me | Theorems.Thm_MatroidProphetKW_RankOne_Supplement_eq_19
-- name    : MatroidProphetKW.RankOne.Supplement.eq_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:06:34.659403+00:00
-- url     : https://prove2.me/theorems/04093e16-fc05-4714-bf57-31f728d9bd8e
-- title:
--   (19) (corrected sort index) — copies virtual surplus ≥ 1/2 (matroid) / 1/(4p − 2) (p matroids) of the expected maximum virtual surplus
-- statement:
--   The setting is that of (18). Values $v_x$ are independent and regular, each with a density positive on its support interval. The constraint is unit-demand and is either a matroid $\mathcal M$, with the thresholds (9) of §3.3, or the intersection of $p\ge1$ matroids, with the §4.2 thresholds at $\alpha=2p$. Thresholds are computed from the laws of $\max(\varphi_x(v_x),0)$. Let $M^{\mathrm{copies}}$ be the mechanism of Algorithm 3, presented in the order of the adversary of Algorithm 2. Then
--   $$\Phi(M^{\mathrm{copies}})=\mathbb E\Big[\sum_{x\in A^{\mathrm{copies}}(v)}\varphi_x(v_x)\Big]\ \ge\ \frac1\alpha\,\mathbb E\Big[\max_{S\in\mathcal I}\sum_{x\in S}\varphi_x(v_x)\Big],$$
--   with $\alpha=2$ for a matroid and $\alpha=4p-2$ for an intersection of $p$ matroids.
--
--   This is the step of the chain (16) where the prophet inequality enters. The adversary is online weight-adaptive. The inverse-price acceptance test uses the original virtual values; clipping is used only to compute the non-negative-weight thresholds.
--
--   **Formalization Note** The right-hand side is the expected maximum virtual surplus over feasible sets. The maximum includes $\emptyset$, so it is non-negative and bounds the virtual surplus of every feasible copies allocation. Regularity makes each positive virtual part integrable even without a finite mean for values: above any point where φ is positive, monotonicity makes it non-negative, and the tail identity ∫_r^R φ(v)f(v)dv = r(1−F(r)) − R(1−F(R)) bounds that tail uniformly. The bounded part below r is integrable. Selected virtual values are non-negative off null price-boundary events.
--
--   Differences from the source:
--
--   - generalization: Φ(OPT^copies), the expected virtual surplus of the optimal mechanism for I^copies → E[max_{S ∈ I} Σ_{x ∈ S} φ_x(v_x)]; reason: the maximum includes every feasible allocation and therefore dominates the virtual surplus of any copies mechanism, OPT^copies included; this implication does not require existence of a revenue-maximizing mechanism or the revenue/virtual-surplus identity for an infinite-mean law
--   - correction: Algorithm 2, line 17 (p. 13) and the proof of (19) sort J_i by p_x + V(A ∪ {x}, i − 1) → the adversary sorts J_i by p_x + V(A ∪ {x}, i); reason: V(A, i) is the revenue from J_{i+1}, …, J_n after J_i, as in preprocessing line 7 and in the proof of (18) on p. 15 (min{p_x + V(A ∪ {x}, i + 1) | x ∈ K} for J_{i+1}); no case is excluded
--   - reading: the thresholds come from the prophet algorithm run on the weights φ_x(v_x), which may be negative, while the algorithms of §§2–4 take non-negative weights → T(A, x) is computed from the laws of max(φ_x(v_x), 0); reason: §2 takes non-negative weights, and downward closure permits discarding negative virtual values without changing the offline maximum; prices still use the original virtual-value inverse, so negative virtual values are rejected even at threshold zero; no equality with the clipped run at that tie is asserted
--   - reading: φ_x^{-1} is not defined when φ_x is not invertible → φ_x^{-1}(t) = inf{v ∈ I_x : φ_x(v) ≥ t}, and +∞ when that set is empty; reason: generalized inverse of a monotone function, equal to the inverse where φ_x is strictly increasing and continuous
--   - reading: M^copies takes T(A, x) from the prophet algorithm run on the adversary's order → thresholds at the set M^copies has allocated so far; reason: the source uses A for its selected services; the local recursion preserves its inverse-price test and advances this actual allocation, including rejection of negative virtual values at threshold zero; the source proof's equality with the online allocation is interpreted using the original virtual-value test, up to null generalized-inverse boundary events
--   - encoding: ties in the adversary's sort are unspecified, groups J_1, …, J_n → ties broken by the fixed enumeration Fintype.equivFin, groups indexed by Fin n (0-based); reason: Lean convention; the sort key is unchanged
--   - encoding: "the intersection of p matroids" → 0 < p; reason: excludes only p = 0, for which no matroid is given and 4p − 2 < 0
--   - reading: Algorithm 2 preprocessing lists stages n through 1, while the proof of (18) uses V(∅,0) → V is defined by (17) also at stage 0, with V(A,n)=0; reason: the definition of V(A,i) as revenue from the remaining groups and the induction on PDF page 16 include i=0; this supplies an omitted table boundary, without changing any ordering or allocation
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 14, (19) and its proof; (16), p. 12; Algorithms 2–3, pp. 13–14

import Mathlib
import Definitions.Def_MatroidProphetKW_Single_Setting
import Definitions.Def_MatroidProphetKW_Single_Algorithm
import Definitions.Def_MatroidProphetKW_Inter_Setting
import Definitions.Def_MatroidProphetKW_RankOne_Supplement_ValueDist
import Definitions.Def_MatroidProphetKW_RankOne_Supplement_Mechanisms

open MeasureTheory

namespace MatroidProphetKW.RankOne.Supplement

/-- (19) (Kleinberg–Weinberg, arXiv:1201.4764v1, p. 14): in a BMUMD setting with independent
regular valuations, the expected virtual surplus of `M^copies` (Algorithm 3) is at
least `1/α` times `E_v[max_{S ∈ ℐ} ∑_{x ∈ S} φ_x(v_x)]`, which bounds
the virtual surplus of every feasible copies allocation: `α = 2` for a matroid
with the thresholds (9) of §3.3, and `α = 4p − 2` for the intersection of `p ≥ 1` matroids with
the thresholds of §4.2 at `α = 2p`. -/
theorem eq_19 {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (owner : α → Fin n)
    (D : α → ValueDist) (hreg : ∀ x, (D x).Regular) :
    (∀ M : Matroid α, M.E = Set.univ → IsUnitDemand (fun S => M.Indep (↑S : Set α)) owner →
      (1 / 2 : ℝ) * ∫ v, MatroidProphetKW.Single.optW M (fun x => (D x).phi (v x)) ∂(prior D) ≤
        copiesVirtualSurplus D (fun S => M.Indep (↑S : Set α))
          (MatroidProphetKW.Single.kwT M (fun x => (D x).wLaw)) owner) ∧
    (∀ (p : ℕ) (M : Fin p → Matroid α), 0 < p → (∀ j, (M j).E = Set.univ) →
      IsUnitDemand (MatroidProphetKW.Inter.IsIndep M) owner →
      1 / (4 * (p : ℝ) - 2) *
          ∫ v, MatroidProphetKW.Inter.OPT M (fun x => (D x).phi (v x)) ∂(prior D) ≤
        copiesVirtualSurplus D (MatroidProphetKW.Inter.IsIndep M)
          (MatroidProphetKW.Inter.Tsum M (fun x => (D x).wLaw) (2 * p)) owner) := by sorry

end MatroidProphetKW.RankOne.Supplement
