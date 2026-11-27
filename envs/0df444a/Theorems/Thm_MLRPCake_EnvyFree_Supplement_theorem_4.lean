-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_Supplement_theorem_4
-- name    : MLRPCake.EnvyFree.Supplement.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:11:34.86314+00:00
-- url     : https://prove2.me/theorems/f5b3a3dc-baed-4656-ab41-edd5ca3851b9
-- title:
--   Theorem 4 — under MLRP an egalitarian-welfare maximizing allocation can be computed up to η in time polynomial in n, log λ and log(1/η)
-- statement:
--   Let $\mathcal C=\langle[n],(f_i)_{i\in[n]}\rangle$ be a cake-division instance whose value densities satisfy MLRP (agents in MLRP order) and whose cut and eval queries are $\lambda$-Lipschitz, $\lambda\ge1$. For every precision $\eta>0$, the algorithm of §8 (binary search for the largest feasible moving-knife target on the grid $\{k/\lceil1/\eta\rceil\}$, then the moving-knife cuts at that target with the leftover cake given to the last agent) returns an allocation $\hat R$, in MLRP order, with
--   $$\mathrm{EW}(\hat R)\ \ge\ \mathrm{EW}(I)-\eta\qquad\text{for every allocation } I,$$
--   using at most $c\,(n+\log_2\lambda+\max(0,\log_2(1/\eta))+1)^c$ Robertson–Webb queries for a universal constant $c$.
--
--   Thus the egalitarian (max–min) welfare can be maximized up to an arbitrary precision in polynomial time under MLRP, although it is APX-hard for general densities.
--
--   Differences from the source:
--   - encoding: agents 1,…,n indexed in the MLRP order (p. 7, w.l.o.g.), densities strictly positive on [0,1] → agents 0,…,n−1 (Fin n) with the published IsMLRP (consecutive ratios f_{i+1}/f_i nondecreasing, f_i > 0 on [0,1]); reason: the paper fixes this indexing and positivity once in §2; same instances
--   - encoding: an instance with n agents, [n] = {1,…,n} → hypothesis 1 ≤ n; reason: excludes only the empty instance, which has no cake division or allocation
--   - encoding: λ ∈ ℝ+ the Lipschitz constant of the cut and eval queries (finite λ ≥ 1, p. 8) → hypotheses 1 ≤ lam and the published QueriesLipschitz f lam; reason: the paper's standing convention on λ (p. 8); same instances
--   - encoding: computed in the Robertson–Webb model in O(poly(n, log λ)) time, up to an arbitrary precision (p. 8: η-close in time polynomial in log(1/η)) → the concrete procedure of §7 (Theorem 3) or §8 (Theorem 4), defined from Cut/Eval answers, and its counted queries and table operations bounded by c·(n + log₂λ + max(0, log₂(1/η)) + 1)^c, c universal and chosen before n, f, λ, η; reason: p. 8 defines arbitrary precision as additive η with polynomial dependence on log(1/η); max(0, ·) only matters for η ≥ 1
--   - encoding: an allocation achieving the optimal egalitarian welfare up to precision η → the output's egalitarian welfare is at least that of every allocation (any assignment order) minus η; reason: equivalent to comparison with the optimum; avoids a real supremum
--   - encoding: binary search over {kη}_{k=0}^{1/η}, with τ = 1 infeasible, and R̂_i of value exactly k₀η for every agent → binary search over k/m, m = ⌈1/η⌉, from (0, m+1) (the sentinel (m+1)/m > 1 is never tested); the last agent receives [MK_{n−1}, 1] with value at least the target; reason: the source presupposes 1/η ∈ ℕ and its claim that τ = 1 is infeasible fails for n = 1; the mesh 1/m ≤ η keeps the precision, and the last agent's extra piece only raises its value
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 9, Theorem 4 (restated and proved pp. 21–22, §8)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions
import Definitions.Def_MLRPCake_EnvyFree_Supplement_MovingKnife

namespace MLRPCake.EnvyFree.Supplement

/-- Theorem 4, p. 9: under MLRP and `λ`-Lipschitz queries, for every `η > 0` the §8 algorithm
(binary search for a feasible moving-knife target on a grid of mesh at most `η`, leftover cake
to the last agent) returns an allocation whose egalitarian welfare is within `η` of the optimum
over all allocations, with work polynomial in `n`, `log λ` and `log(1/η)`. -/
theorem theorem_4 : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam η : ℝ),
    1 ≤ n → IsInstance f → IsMLRP f → 1 ≤ lam → QueriesLipschitz f lam → 0 < η →
    IsAllocation (n := n) (ewOutput f η) ∧
      (∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x →
        EW f x σ - η ≤ EW f (ewOutput f η) (Equiv.refl (Fin n))) ∧
      (ewCost n η : ℝ) ≤
        c * ((n : ℝ) + Real.logb 2 lam + max 0 (Real.logb 2 (1 / η)) + 1) ^ c := by sorry

end MLRPCake.EnvyFree.Supplement
