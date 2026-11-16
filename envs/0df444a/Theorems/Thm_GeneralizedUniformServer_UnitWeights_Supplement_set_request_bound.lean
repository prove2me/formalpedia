-- Prove2me | Theorems.Thm_GeneralizedUniformServer_UnitWeights_Supplement_set_request_bound
-- name    : GeneralizedUniformServer.UnitWeights.Supplement.set_request_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:41:47.990602+00:00
-- url     : https://prove2.me/theorems/4484a60e-bd93-4add-a6c7-8625581823f2
-- title:
--   Theorem 3.5 — for set requests of at most $B$ points the §3.3 algorithm has $\mathbb E[\mathrm{ALG}(\rho)]\le(k+1)\ln(2B)\,\mathrm{OPT}(\rho)$
-- statement:
--   Let $M_1,\dots,M_k$ be uniform metric spaces with unit distances, of arbitrary cardinality, and $a\in X$ an initial configuration. Suppose every request $P$ specifies finite sets $P_i\subseteq M_i$, is served by $x$ if $x_i\in P_i$ for some $i$, and has
--   $$1\le n(P)=\sum_{i=1}^k|P_i|\le B .$$
--   Run the algorithm of §3.3 from $a$: stay if the current configuration serves the request; otherwise, with probability $1/2$ move to a uniformly random one of the $n(P)$ repairs, and with probability $1/2$ move to a fresh draw from $\mu_t=\phi_t/\Phi_t$, where each failing configuration passes the fraction $1/(2n(P))$ of its weight to each of its repairs. Then for every finite request sequence $\rho$,
--   $$\mathbb E[\mathrm{ALG}(\rho)]\le(k+1)\ln(2B)\cdot\mathrm{OPT}(\rho),$$
--   where costs are Hamming distances and $\mathrm{OPT}(\rho)$ is the cost of an optimal offline solution from $a$ for the set requests.
--
--   This extends Theorem 1.1 (the case $P_i=\{r_i\}$, $B=k$) and gives the ratio $(k+1)\ln(2k)$ for paging with heterogeneous cache slots and $(k+1)\ln(2k\ell)$ for metrical service systems with $k$ servers on a uniform metric and requests of $\ell$ points.
--
--   **Formalization Note** The expected cost is computed in $[0,\infty]$ from the algorithm's joint trajectory law and compared with `ENNReal.ofReal` of the right-hand side, which is nonnegative. The hypothesis on the sizes is imposed on each request of $\rho$. The logarithm is natural.
--
--   Differences from the source:
--   - encoding: real-valued expected Hamming cost and the minimum offline cost → expected cost in ENNReal compared with ENNReal.ofReal of the bound, with setOptCost defined by a natural-number infimum; reason: every step costs at most k and every valid request has a repair, so the expectation is finite and the nonempty natural cost set attains its minimum; the bound is nonnegative.
--   - encoding: pairwise disjoint uniform metric spaces indexed by 1 through k → dependent coordinate types indexed by Fin k, with coordinate movement costs defined explicitly; reason: tagging each coordinate makes the spaces disjoint, and shifting the index labels changes no configuration, request, or cost.
--   - encoding: finite point sets, their repairs, and the algorithm of Sections 3.2 and 3.3 → dependent Finsets, repair pairs (i,p), finitely supported weights and history-dependent PMF transitions; reason: for a failing configuration repair pairs are in bijection with distinct repairs; the finite sums and joint trajectory law implement exactly the fair repair-or-resample rule.
--   - generalization: the standing assumption k ≥ 1 and the positive request-size bound implicit in ln(2B) → k and B may be zero; reason: if k = 0 or B = 0 the request-size hypothesis forces the sequence to be empty; its movement cost and offline optimum are zero, and the totalized logarithm makes the displayed inequality 0 ≤ 0; all source instances with k,B ≥ 1 remain included.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 10, Theorem 3.5 (§3.3)

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_SetRequests

namespace GeneralizedUniformServer.UnitWeights.Supplement

/-- Theorem 3.5 (source p. 10): for requests that specify sets of at most `B` points in total
(every request `P` of `ρ` has `1 ≤ ∑ᵢ |Pᵢ| ≤ B`), the algorithm of §3.3 started at `a`
satisfies `E[ALG(ρ)] ≤ (k + 1) ln(2B) · OPT(ρ)` for every finite request sequence `ρ`, where
`OPT(ρ)` is the cost of an optimal set-request offline solution starting from `a`. -/
theorem set_request_bound {k : ℕ} {M : Fin k → Type*} (a : Config M) (B : ℕ)
    (ρ : List (SetRequest M)) (hρ : ∀ P ∈ ρ, 1 ≤ reqSize P ∧ reqSize P ≤ B) :
    genExpectedCost (setAlg a) a ρ ≤
      ENNReal.ofReal (((k : ℝ) + 1) * Real.log (2 * (B : ℝ)) * (setOptCost a ρ : ℝ)) := by sorry

end GeneralizedUniformServer.UnitWeights.Supplement
