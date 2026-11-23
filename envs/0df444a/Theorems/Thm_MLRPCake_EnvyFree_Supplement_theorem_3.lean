-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_Supplement_theorem_3
-- name    : MLRPCake.EnvyFree.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:10:16.266724+00:00
-- url     : https://prove2.me/theorems/4a43ef42-8820-4204-8c51-8abe58a060db
-- title:
--   Theorem 3 — under MLRP a social-welfare maximizing allocation can be computed up to η in time polynomial in n, log λ and log(1/η)
-- statement:
--   Let $\mathcal C=\langle[n],(f_i)_{i\in[n]}\rangle$ be a cake-division instance whose value densities satisfy MLRP (agents in MLRP order) and whose cut and eval queries are $\lambda$-Lipschitz, $\lambda\ge1$. For every precision $\eta>0$, the algorithm of §7 (localize every switching point $p_{ij}$ within $\eta/(n\lambda)$ by Corollary 1, sort the estimates together with $0$ and $1$, and run the social-welfare dynamic program on them) returns an allocation $\hat S$, in MLRP order, with
--   $$\mathrm{SW}(\hat S)\ \ge\ \mathrm{SW}(I)-\eta\qquad\text{for every allocation } I,$$
--   using a number of Robertson–Webb queries and dynamic-programming operations at most $c\,(n+\log_2\lambda+\max(0,\log_2(1/\eta))+1)^c$ for a universal constant $c$.
--
--   Thus social welfare can be maximized up to an arbitrary precision in time polynomial in $n$, $\log\lambda$ and $\log(1/\eta)$, in contrast to the polynomial dependence on $1/\eta$ of a uniform value grid.
--
--   Differences from the source:
--   - encoding: agents 1,…,n indexed in the MLRP order (p. 7, w.l.o.g.), densities strictly positive on [0,1] → agents 0,…,n−1 (Fin n) with the published IsMLRP (consecutive ratios f_{i+1}/f_i nondecreasing, f_i > 0 on [0,1]); reason: the paper fixes this indexing and positivity once in §2; same instances
--   - encoding: an instance with n agents, [n] = {1,…,n} → hypothesis 1 ≤ n; reason: excludes only the empty instance, which has no cake division or allocation
--   - encoding: λ ∈ ℝ+ the Lipschitz constant of the cut and eval queries (finite λ ≥ 1, p. 8) → hypotheses 1 ≤ lam and the published QueriesLipschitz f lam; reason: the paper's standing convention on λ (p. 8); same instances
--   - encoding: computed in the Robertson–Webb model in O(poly(n, log λ)) time, up to an arbitrary precision (p. 8: η-close in time polynomial in log(1/η)) → the concrete procedure of §7 (Theorem 3) or §8 (Theorem 4), defined from Cut/Eval answers, and its counted queries and table operations bounded by c·(n + log₂λ + max(0, log₂(1/η)) + 1)^c, c universal and chosen before n, f, λ, η; reason: p. 8 defines arbitrary precision as additive η with polynomial dependence on log(1/η); max(0, ·) only matters for η ≥ 1
--   - encoding: an allocation achieving the optimal social welfare up to precision η → the output's social welfare is at least that of every allocation (any assignment order) minus η; reason: equivalent to comparison with the optimum; avoids a real supremum
--   - encoding: dynamic program M(k,t) = max_{1≤t′≤t} M(k−1,t′) + v_k(p̂_t′, p̂_t) with M(1,t) = v_1(0, p̂_t) → the same recursion with predecessor index 0 allowed and p̂_ij taken as the left endpoint of the localized interval; reason: index 0 lets an agent receive an empty initial piece, as the optimal allocation may require; any point of the localized interval is within η/(nλ) of p_ij
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 9, Theorem 3 (restated and proved pp. 19–20, §7)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SocialDP

namespace MLRPCake.EnvyFree.Supplement

/-- Theorem 3, p. 9: under MLRP and `λ`-Lipschitz queries, for every `η > 0` the §7 algorithm
(localize every switching point within `η/(nλ)`, then run the dynamic program on the sorted
estimates) returns an allocation whose social welfare is within `η` of the optimum over all
allocations, with work polynomial in `n`, `log λ` and `log(1/η)` (universal polynomial). -/
theorem theorem_3 : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam η : ℝ),
    1 ≤ n → IsInstance f → IsMLRP f → 1 ≤ lam → QueriesLipschitz f lam → 0 < η →
    IsAllocation (n := n) (swOutput f lam η) ∧
      (∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x →
        SW f x σ - η ≤ SW f (swOutput f lam η) (Equiv.refl (Fin n))) ∧
      (swCost f lam η : ℝ) ≤
        c * ((n : ℝ) + Real.logb 2 lam + max 0 (Real.logb 2 (1 / η)) + 1) ^ c := by sorry

end MLRPCake.EnvyFree.Supplement
