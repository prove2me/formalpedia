-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_theorem_6
-- name    : MLRPCake.EnvyFree.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:20.001989+00:00
-- url     : https://prove2.me/theorems/57b57b27-e748-4dac-a81e-cbefd325419f
-- title:
--   Theorem 6, p. 13 — under MLRP every δ-ripple division induces an envy-free partial allocation
-- statement:
--   Let $\mathcal C=\langle[n],\{f_i\}_i\rangle$ be a cake-division instance in which the value densities satisfy the monotone likelihood ratio property, with the agents indexed in the MLRP order, and let $\delta\ge0$. Let $x_0=0\le x_1\le\dots\le x_n\le1$ be a $\delta$-ripple division of $\mathcal C$, and let $I_i=[x_{i-1},x_i]$. Then the partial allocation $\{I_1,\dots,I_n\}$ is envy-free:
--   $$v_i(I_i)\ge v_i(I_j)\qquad\text{for all }i,j\in[n].$$
--
--   At most the $\delta$-length piece $[x_n,1]$ of the cake remains unallocated. With $\delta=0$, every exact ripple division induces an envy-free allocation.
--
--   **Formalization Note** Agents are 0-based, and agent $i$ receives `[x i, x (i+1)]`. The MLRP order is the agents' indexing (the paper's w.l.o.g. convention, p. 7).
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 13, Theorem 6 (proof pp. 13–14)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree

/-- Theorem 6, p. 13: under MLRP, for every `δ ≥ 0`, every `δ`-ripple division induces an
envy-free partial allocation `I_i = [x_{i-1}, x_i]`. -/
theorem theorem_6 (n : ℕ) (f : Fin n → ℝ → ℝ) (δ : ℝ) (x : ℕ → ℝ) (hf : IsInstance f)
    (hmlrp : IsMLRP f) (hδ : 0 ≤ δ) (hx : IsRipple f δ x) :
    ∀ i j : ℕ, i < n → j < n → val f i (x j) (x (j + 1)) ≤ val f i (x i) (x (i + 1)) := by sorry

end MLRPCake.EnvyFree
