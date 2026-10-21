-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_coalesce_envy_free
-- name    : MLRPCake.EnvyFree.coalesce_envy_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:23.981065+00:00
-- url     : https://prove2.me/theorems/63c08e84-3a71-4b4d-b721-965d3e562604
-- title:
--   Proof of Theorem 1, p. 15 — coalescing [x_n, 1] into the last piece of an (η/λ)-ripple division gives envy-freeness up to η
-- statement:
--   Let $\mathcal C=\langle[n],\{f_i\}_i\rangle$ be a cake-division instance with $n\ge1$ agents whose value densities satisfy the monotone likelihood ratio property (agents indexed in the MLRP order), with $\lambda$-Lipschitz cut and eval queries for some $\lambda\ge1$, and let $\eta>0$. Let $x_0=0\le x_1\le\dots\le x_n\le1$ be an $(\eta/\lambda)$-ripple division, and let $I_i=[x_{i-1},x_i]$. Write $\mathcal I^*=\{I^*_1,\dots,I^*_n\}$ for the allocation in which the $n$th agent receives $I^*_n:=[x_{n-1},1]$ (equivalently $I^*_n=I_n\cup[x_n,1]$) and $I^*_i=I_i$ for the remaining agents $i\in[n-1]$. Then $\mathcal I^*$ is a contiguous allocation of the whole cake, and it is envy-free up to $\eta$ precision:
--   $$v_i(I^*_i)\ge v_i(I^*_j)-\eta\qquad\text{for all }i,j\in[n].$$
--
--   This is the step that turns BinSearch's partial allocation into the complete allocation of Theorem 1.
--
--   **Formalization Note** The allocation $\mathcal I^*$ is obtained from the cut points by replacing $x_n$ with $1$. $\lambda\ge1$ is the paper's standing assumption.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 15, proof of Theorem 1 (§5.4)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree

/-- Proof of Theorem 1, p. 15: under MLRP and `λ`-Lipschitz queries, giving the unallocated
piece `[x_n, 1]` of an `(η/λ)`-ripple division to the last agent yields a complete contiguous
allocation that is envy-free up to `η`. -/
theorem coalesce_envy_free (n : ℕ) (f : Fin n → ℝ → ℝ) (lam η : ℝ) (x : ℕ → ℝ) (hn : 1 ≤ n)
    (hf : IsInstance f) (hmlrp : IsMLRP f) (hlam : 1 ≤ lam) (hL : QueriesLipschitz f lam)
    (hη : 0 < η) (hx : IsRipple f (η / lam) x) :
    IsAllocation (n := n) (coalesce n x) ∧ EnvyFreeUpTo f η (coalesce n x) := by sorry

end MLRPCake.EnvyFree
