-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_Supplement_theorem_5
-- name    : MLRPCake.EnvyFree.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:12:11.412976+00:00
-- url     : https://prove2.me/theorems/790e13c6-0992-4285-ba7a-a137d5765638
-- title:
--   Theorem 5 — under MLRP an allocation with Nash social welfare at least (1−ε)·OPT can be computed in time polynomial in n, 1/ε and log λ
-- statement:
--   Let $\mathcal C=\langle[n],(f_i)_{i\in[n]}\rangle$ be a cake-division instance whose value densities satisfy MLRP (agents in MLRP order) and whose cut and eval queries are $\lambda$-Lipschitz, $\lambda\ge1$. For every $\varepsilon>0$, the algorithm of §9 (the value grid $c_t$ with cells worth at most $\varepsilon/(8n)$ to every agent, then the Nash-product dynamic program on it) returns an allocation $\hat A$, in MLRP order, with
--   $$\mathrm{NSW}(\hat A)\ \ge\ (1-\varepsilon)\,\mathrm{NSW}(I)\qquad\text{for every allocation } I,$$
--   using at most $c\,(n+1/\varepsilon+\log_2\lambda+1)^c$ Robertson–Webb queries and dynamic-programming operations for a universal constant $c$.
--
--   Maximizing Nash social welfare therefore admits a fully polynomial-time approximation scheme under MLRP. The factor $1-\varepsilon$ applies to the geometric mean, not only to the product.
--
--   Differences from the source:
--   - encoding: agents 1,…,n indexed in the MLRP order (p. 7, w.l.o.g.), densities strictly positive on [0,1] → agents 0,…,n−1 (Fin n) with the published IsMLRP (consecutive ratios f_{i+1}/f_i nondecreasing, f_i > 0 on [0,1]); reason: the paper fixes this indexing and positivity once in §2; same instances
--   - encoding: an instance with n agents, [n] = {1,…,n} → hypothesis 1 ≤ n; reason: excludes only the empty instance, which has no cake division or allocation
--   - encoding: λ ∈ ℝ+ the Lipschitz constant of the cut and eval queries (finite λ ≥ 1, p. 8) → hypotheses 1 ≤ lam and the published QueriesLipschitz f lam; reason: the paper's standing convention on λ (p. 8); same instances
--   - encoding: computed in time polynomial in 1/ε, log λ and n → the concrete §9 procedure and its counted queries and table operations bounded by c·(n + 1/ε + log₂λ + 1)^c, c universal and chosen before n, f, λ, ε; reason: same polynomial dependence; the constant is uniform over instances
--   - encoding: Nash social welfare at least (1 − ε) times the optimal → (1 − ε)·NSW(I) ≤ NSW(output) for every allocation I (any assignment order), every ε > 0; reason: equivalent to comparison with the optimum; for ε ≥ 1 the claim is the nonnegativity of NSW
--   - encoding: grid c_0,…,c_N with N ≤ 8n²/ε and H(k,t) = max_{1≤t′≤t} H(k−1, c_t′)·v_k(c_t′, c_t) → grid c_0,…,c_N with N = ⌈8n²/ε⌉ + 1 and the recursion with H(k−1, t′) and predecessor index 0 allowed; reason: an integer grid length covering the source bound; H(k−1, c_t′) is an index slip for H(k−1, t′); index 0 allows empty initial pieces
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 9, Theorem 5 (restated and proved pp. 22–23, §9)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions
import Definitions.Def_MLRPCake_EnvyFree_Supplement_NashDP

namespace MLRPCake.EnvyFree.Supplement

/-- Theorem 5, p. 9: under MLRP and `λ`-Lipschitz queries, for every `ε > 0` the §9 algorithm
(value grid of cells worth at most `ε/(8n)` to every agent, then the Nash-product dynamic
program) returns an allocation whose Nash social welfare is at least `(1 - ε)` times that of
every allocation, with work polynomial in `n`, `1/ε` and `log λ`. -/
theorem theorem_5 : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam ε : ℝ),
    1 ≤ n → IsInstance f → IsMLRP f → 1 ≤ lam → QueriesLipschitz f lam → 0 < ε →
    IsAllocation (n := n) (nashOutput f ε) ∧
      (∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x →
        (1 - ε) * NSW f x σ ≤ NSW f (nashOutput f ε) (Equiv.refl (Fin n))) ∧
      (nashCost n ε : ℝ) ≤ c * ((n : ℝ) + 1 / ε + Real.logb 2 lam + 1) ^ c := by sorry

end MLRPCake.EnvyFree.Supplement
