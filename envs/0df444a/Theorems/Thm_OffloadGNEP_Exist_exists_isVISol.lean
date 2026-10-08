-- Prove2me | Theorems.Thm_OffloadGNEP_Exist_exists_isVISol
-- name    : OffloadGNEP.Exist.exists_isVISol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:32.444972+00:00
-- url     : https://prove2.me/theorems/2e136346-331c-48af-827d-03f23f3f0dc6
-- title:
--   Proof of Proposition 1, p. 12 — VI(K, F) has a solution (by [17, Corollary 2.2.5])
-- statement:
--   Assume Assumption A and the standing hypotheses, and assume that every private feasible set $\tilde K_u$ is nonempty. Then the variational inequality $\mathrm{VI}(K,F)$ has a solution: there is $\bar x\in K$ with
--   $$F(\bar x)^\top(x-\bar x)\ge0\qquad\text{for all }x\in K.$$
--
--   This is the existence of a variational solution of the offloading game, the solution the distributed algorithms of the paper compute.
--
--   **Formalization Note** The nonemptiness of every $\tilde K_u$ is added to the paper's hypotheses. It is equivalent to $K\neq\emptyset$ (moving the cloudlet share of a point of $\tilde K_u$ to the cloud keeps it in $\tilde K_u$ and makes the load $0\le U_{\max}$), and without it the statement is false: if $0<P_{u,\max}<\min(\alpha_uP_{u,m},\beta_uP_{u,t})$ then $\tilde K_u=\emptyset$, so $K=\emptyset$.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 12, proof of Proposition 1 (citing [17, Corollary 2.2.5])

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

namespace OffloadGNEP.Exist

/-- Proof of Proposition 1, p. 12 (citing [17, Corollary 2.2.5]): VI(K, F) has a solution.
The hypothesis that every `K̃_u` is nonempty is a disclosed addition (equivalent to `K ≠ ∅`);
without it `K` can be empty and no solution exists. -/
theorem exists_isVISol {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hne : ∀ u, (Ktil P u).Nonempty) : ∃ xb, IsVISol (K P) (F P) xb := by sorry

end OffloadGNEP.Exist
