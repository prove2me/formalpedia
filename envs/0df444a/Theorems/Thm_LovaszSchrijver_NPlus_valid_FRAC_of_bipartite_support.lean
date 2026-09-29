-- Prove2me | Theorems.Thm_LovaszSchrijver_NPlus_valid_FRAC_of_bipartite_support
-- name    : LovaszSchrijver.NPlus.valid_FRAC_of_bipartite_support
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:00:30.410215+00:00
-- url     : https://prove2.me/theorems/22e1184f-bf7e-424b-a8d8-66878ab5e8ef
-- title:
--   Section 2.c remark — an inequality whose nonzero-coefficient nodes induce a bipartite graph has N-index 0
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes, and let $a^{\mathsf T}x \le b$ ($a \in \mathbb R^V$, $b \in \mathbb R$) be valid for $\mathrm{STAB}(G)$. The paper remarks (p. 179) that "the index of an inequality depends only on the subgraph induced by those nodes having a nonzero coefficient. In particular, if these nodes induce a bipartite graph, then the inequality has $N$-index 0."
--
--   Formally: if the subgraph of $G$ induced by $\{i \in V : a_i \ne 0\}$ is bipartite (2-colourable), then
--   $$a^{\mathsf T}x \le b \quad \text{for all } x \in \mathrm{FRAC}(G).$$
--
--   Since $N^0(G) = N_+^0(G) = \mathrm{FRAC}(G)$, this says the inequality has $N$-index and $N_+$-index $0$. It is the base case of the paper's proof that clique, odd hole, odd wheel and odd antihole constraints have $N_+$-index 1.
--
--   **Formalization Note** No sign condition is placed on $a$. The standing hypothesis that $G$ has no isolated nodes is needed: a node with no neighbours is unbounded in $\mathrm{FRAC}(G)$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 179, Section 2.c

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet

namespace LovaszSchrijver.NPlus

theorem valid_FRAC_of_bipartite_support {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) (b : ℝ)
    (hvalid : Valid (STAB G) a b) (hbip : (G.induce {i | a i ≠ 0}).Colorable 2) :
    Valid (FRAC G) a b := by sorry

end LovaszSchrijver.NPlus
