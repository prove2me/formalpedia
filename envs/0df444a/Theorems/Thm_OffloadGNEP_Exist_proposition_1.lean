-- Prove2me | Theorems.Thm_OffloadGNEP_Exist_proposition_1
-- name    : OffloadGNEP.Exist.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:07.535889+00:00
-- url     : https://prove2.me/theorems/673cc5ef-822b-4189-9c49-244bbe514d1a
-- title:
--   Proposition 1, p. 12 — under Assumption A the offloading GNEP (10)–(15) has at least one solution
-- statement:
--   Consider the computation-offloading game (10)–(15) with $N$ users, $n\ge1$ cloudlet servers and offloadable fraction $0<\chi\le1$. Suppose Assumption A holds,
--   $$0<U_{\max}<1,\qquad 0<\alpha_u<1,\qquad 0<\delta_u<1\qquad(u=1,\dots,N),$$
--   and that every user's private feasible set $\tilde K_u$ is nonempty. Then the GNEP has at least one solution: there is a profile $\bar x\in K$ such that, for every user $u$, $\bar x_u$ minimises $\lambda_uR_u(\cdot,\bar x_{-u})$ over $\{y\in\tilde K_u:(y,\bar x_{-u})\in\Omega\}$.
--
--   Existence of an equilibrium is the starting point of the paper's analysis: the authors then single out the variational solutions and compute them by a distributed algorithm.
--
--   **Formalization Note** The hypothesis "$\tilde K_u\neq\emptyset$ for every $u$" is not printed in the proposition. It is added because the printed statement is false without it: if $0<P_{u,\max}<\min(\alpha_uP_{u,m},\beta_uP_{u,t})$ for some $u$, then every $x_u\ge0$ with $\sum_ix_{u,i}=1$ violates (12), so $K=\emptyset$ and no solution exists (for instance $N=n=1$, $\alpha=\beta=\delta=U_{\max}=\tfrac12$, $\chi=1$, $P_{u,m}=P_{u,t}=1$, $P_{u,\max}=0$). The condition is equivalent to $K\ne\emptyset$. The standing hypotheses $n\ge1$ and $0<\chi\le1$ come from pp. 7 and 9. A GNEP solution keeps the shared constraint $\Omega$ in each player's feasible set.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 12, Proposition 1

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

namespace OffloadGNEP.Exist

/-- Proposition 1, p. 12: supposing that Assumption A holds, the GNEP (10)–(15) has at least one
solution. The hypothesis that every `K̃_u` is nonempty is a disclosed addition: if
`0 < P_{u,max} < min(α_u P_{u,m}, β_u P_{u,t})` then `K̃_u = ∅` and the GNEP has no solution. -/
theorem proposition_1 {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hne : ∀ u, (Ktil P u).Nonempty) : ∃ xb, IsGNEPSol P xb := by sorry

end OffloadGNEP.Exist
