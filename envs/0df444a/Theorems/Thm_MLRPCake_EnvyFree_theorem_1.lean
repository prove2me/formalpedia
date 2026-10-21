-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_theorem_1
-- name    : MLRPCake.EnvyFree.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:19.501424+00:00
-- url     : https://prove2.me/theorems/2eb5401a-f389-4b24-9239-b3a92935e67a
-- title:
--   Theorem 1, p. 8 — under MLRP, BinSearch finds an allocation envy-free up to η in poly(n, log λ, log 1/η) iterations
-- statement:
--   There is a universal constant $c\in\mathbb N$ such that the following holds. Let $\mathcal C=\langle[n],(f_i)_{i\in[n]}\rangle$ be a cake-division instance with $n\ge1$ agents in which the value densities satisfy the monotone likelihood ratio property, with the agents indexed in the MLRP order. Assume the cut and eval queries are $\lambda$-Lipschitz for some $\lambda\ge1$, and let $\eta\in(0,1)$ be the precision. Run BinSearch (Algorithm 1) with parameter $\delta=\eta/\lambda$. Then:
--
--   1. BinSearch returns at its first stopping iteration $T$, and
--   $$T\le c\,\big(n+\log_2\lambda+\log_2(1/\eta)+1\big)^{c};$$
--   2. coalescing its output (giving the leftover piece $[x_n,1]$ to agent $n$) yields a contiguous allocation $\mathcal I=\{I_1,\dots,I_n\}$ of the whole cake $[0,1]$ that is envy-free up to precision $\eta$: $v_i(I_i)\ge v_i(I_j)-\eta$ for all $i,j\in[n]$.
--
--   This is the paper's Theorem 1: under MLRP, an envy-free allocation with connected pieces can be computed up to an arbitrary precision in $O(\mathrm{poly}(n,\log\lambda))$ time in the Robertson–Webb query model. The time is polynomial in $\log(1/\eta)$, so $\eta$ can be driven exponentially close to zero.
--
--   **Formalization Note** The running time is measured in iterations of BinSearch. Each iteration evaluates $\mathrm{RD}_n$ once, at a cost of $2(n-1)$ Robertson–Webb queries. The polynomial is universal: $c$ is chosen before $n$ and the instance. The restriction $\eta<1$ is added: the paper's proof uses $\delta=\eta/\lambda\in(0,1)$, and for $\eta\ge1$ envy-freeness up to $\eta$ is automatic. $\lambda\ge1$ is the paper's standing assumption (p. 8). Riemann integrability is encoded as boundedness plus interval integrability.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 8, Theorem 1 (precision notion p. 8; restated p. 14; proof §5.4, pp. 14–15)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree

/-- Theorem 1, p. 8: under MLRP and `λ`-Lipschitz queries, BinSearch run with `δ = η/λ`
returns within a number of iterations polynomial in `n`, `log λ` and `log (1/η)` (with a
universal polynomial; each iteration costs `2(n-1)` Robertson–Webb queries), and coalescing its
output gives a contiguous allocation that is envy-free up to `η`. -/
theorem theorem_1 : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam η : ℝ),
    1 ≤ n → IsInstance f → IsMLRP f → 1 ≤ lam → QueriesLipschitz f lam → 0 < η → η < 1 →
    ∃ T : ℕ, bsStops f (η / lam) T ∧ (∀ k < T, ¬ bsStops f (η / lam) k) ∧
      (T : ℝ) ≤ c * ((n : ℝ) + Real.logb 2 lam + Real.logb 2 (1 / η) + 1) ^ c ∧
      IsAllocation (n := n) (coalesce n (bsOutput f (η / lam) T)) ∧
      EnvyFreeUpTo f η (coalesce n (bsOutput f (η / lam) T)) := by sorry

end MLRPCake.EnvyFree
