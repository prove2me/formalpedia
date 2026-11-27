-- Prove2me | Theorems.Thm_MulticlassQNet_SingleStation_Supplement_theorem_5_1_routing_polyhedron
-- name    : MulticlassQNet.SingleStation.Supplement.theorem_5_1_routing_polyhedron
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:31:17.86616+00:00
-- url     : https://prove2.me/theorems/e2e3997d-3111-41e4-a7c4-c503eea58ebf
-- title:
--   Theorem 5.1 — the achievable (n, u, D, G, I) under routing and sequencing lies in the polyhedron (36)–(42) (corrected: no u factor on the right of (38); free index j in (40))
-- statement:
--   Consider an open multiclass network in which both sequencing and routing are controlled (§5): for each class $r$ a set $F_r$ of allowed targets (classes, and possibly the exit $0$) is given, and a policy chooses, from the current state, which classes to serve and a routing distribution $p_{r\cdot}$ supported on $F_r$. Under a policy satisfying Assumption A, let $n_r=E[n_r]$ and let $u_r$, $D_{rr'}$, $G_{rr'j}$, $I_{rj}$ be the stationary moments (32)–(35), the index $r'$ ranging over classes and the exit $0$.
--
--   Then for every such policy:
--
--   $$\mu_ru_r-\sum_{l=1}^R\mu_lD_{lr}=\lambda_{0r},\qquad r=1,\dots,R,\qquad(36)$$
--
--   $$2\mu_rI_{rr}-2\sum_{l=1}^R\mu_lG_{lrr}-2\lambda_{0r}n_r=\lambda_{0r}+\mu_r(u_r-D_{rr})+\sum_{l\ne r}\mu_lD_{lr},\qquad r=1,\dots,R,\qquad(37)$$
--
--   $$\mu_rI_{rr'}+\mu_{r'}I_{r'r}-\sum_{w=1}^R\mu_wG_{wrr'}-\sum_{w=1}^R\mu_wG_{wr'r}-\lambda_{0r}n_{r'}-\lambda_{0r'}n_r=-\mu_rD_{rr'}-\mu_{r'}D_{r'r},\qquad r>r',\qquad(38)$$
--
--   $$\sum_{r\in C_i}u_r\le1,\ \ i=1,\dots,N,\qquad(39)\qquad\qquad \sum_{r\in C_i}I_{rj}\le n_j,\ \ j=1,\dots,R,\ i=1,\dots,N,\qquad(40)$$
--
--   $$u_r=\sum_{l=0}^RD_{rl},\qquad(41)\qquad\qquad I_{rj}=\sum_{l=0}^RG_{rlj},\qquad(42)$$
--
--   $D_{rr'}=G_{rr'j}=0$ whenever $r'\notin F_r$, and all of $n_r,u_r,D_{rr'},G_{rr'j},I_{rj}$ are nonnegative.
--
--   Minimizing a linear cost over this polyhedron gives a lower bound for the joint routing-and-sequencing problem, with $O(R^3)$ variables.
--
--   **Formalization Note** Routing targets are `Option (Fin R)`, with `none` the exit. Policies, Assumption A and the moments are those of the `Routing` definition; $n_r$ is the published `meanNum`. The conclusion holds for the actual moments of every admissible policy; nothing about (36)–(42) is assumed.
--
--   Differences from the source:
--   - correction: the right-hand side of (38) is printed $-\mu_ru_rD_{rr'}-\mu_{r'}u_{r'}D_{r'r}$ → Lean has $-\mu_rD_{rr'}-\mu_{r'}D_{r'r}$; reason: $D_{rr'}$ already contains $1\{B_r\}$ by (33), and expanding the mixed term of the $R^2$ drift gives exactly $-\mu_rD_{rr'}-\mu_{r'}D_{r'r}$ (a stable tandem with $\lambda_{01}=1/4$, $\mu_1=\mu_2=1$ gives $-1/4$ on the left of (38) against $-1/16$ printed)
--   - correction: (40) is indexed "$r=1,\dots,R$" after a sum binding $r$, with $j$ free → Lean quantifies over $j$ and $i$; reason: dummy-index typo, fixed by definition (35) and the analogous (46), (51)
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), pp. 23–24, Theorem 5.1, Eqs. (36)–(42); definitions (32)–(35), p. 23; proof p. 24

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_Routing

namespace MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 5.1 (pp. 23–24): for every routing-and-sequencing policy satisfying Assumption A,
the stationary quantities `n_r`, `u_r` (32), `D_{rd}` (33), `G_{rdj}` (34), `I_{rj}` (35) satisfy
(36)–(42), vanish on routes outside `F_r`, and are nonnegative. In (38) the right-hand side is
`−μ_r D_{rr'} − μ_{r'} D_{r'r}` (the printed `u_r D_{rr'}` products double-count `u`, since (33)
already includes `1{B_r}`); in (40) the free index is `j`. The exit target is `none`. -/
theorem theorem_5_1_routing_polyhedron {N R : ℕ} (net : Network N R)
    (F : Fin R → Finset (Option (Fin R))) (P : RoutingPolicy net F) (π : (Fin R → ℕ) → ℝ)
    (hA : P.AssumptionA π) :
    -- (36)
    (∀ r, net.μ r * P.u π r - ∑ l, net.μ l * P.D π l (some r) = net.lam0 r) ∧
    -- (37)
    (∀ r, 2 * net.μ r * P.I π r r - 2 * ∑ l, net.μ l * P.G π l (some r) r
        - 2 * net.lam0 r * meanNum π r
      = net.lam0 r + net.μ r * (P.u π r - P.D π r (some r))
        + ∑ l ∈ Finset.univ.erase r, net.μ l * P.D π l (some r)) ∧
    -- (38), corrected right-hand side
    (∀ r r', r' < r →
      net.μ r * P.I π r r' + net.μ r' * P.I π r' r - ∑ w, net.μ w * P.G π w (some r) r'
        - ∑ w, net.μ w * P.G π w (some r') r - net.lam0 r * meanNum π r'
        - net.lam0 r' * meanNum π r
      = -(net.μ r * P.D π r (some r')) - net.μ r' * P.D π r' (some r)) ∧
    -- (39)
    (∀ i, ∑ r ∈ net.C i, P.u π r ≤ 1) ∧
    -- (40)
    (∀ i j, ∑ r ∈ net.C i, P.I π r j ≤ meanNum π j) ∧
    -- (41)
    (∀ r, P.u π r = ∑ d, P.D π r d) ∧
    -- (42)
    (∀ r j, P.I π r j = ∑ d, P.G π r d j) ∧
    -- forbidden routes
    (∀ r d, d ∉ F r → P.D π r d = 0 ∧ ∀ j, P.G π r d j = 0) ∧
    -- nonnegativity
    (∀ r, 0 ≤ meanNum π r) ∧ (∀ r, 0 ≤ P.u π r) ∧ (∀ r d, 0 ≤ P.D π r d) ∧
    (∀ r d j, 0 ≤ P.G π r d j) ∧ (∀ r j, 0 ≤ P.I π r j) := by sorry

end MulticlassQNet.SingleStation.Supplement
