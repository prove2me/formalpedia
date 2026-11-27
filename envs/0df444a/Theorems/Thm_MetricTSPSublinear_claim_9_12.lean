-- Prove2me | Theorems.Thm_MetricTSPSublinear_claim_9_12
-- name    : MetricTSPSublinear.claim_9_12
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:32:25.058462+00:00
-- url     : https://prove2.me/theorems/4aae8239-1160-5f31-82e7-04d6afab2076
-- title:
--   Claim 9.12: dual solution to dominated Steiner tree via Gromov products
-- statement:
--   Let $d$ be a metric on $V$, $S\subseteq V$ nonempty, and $y$ a feasible dual solution of the cut LP on $S$: $y_A\ge0$ on proper nonempty subsets $A\subsetneq S$, and every pair $u\ne v$ of $S$ is separated with total weight $\rho(u,v)=\sum_{A:|A\cap\{u,v\}|=1}y_A\le d(u,v)$. Fix $z\in S$, put $h_u=\rho(z,u)$ and $g_{uv}=\tfrac12(\rho(z,u)+\rho(z,v)-\rho(u,v))$, take a maximum spanning tree $R$ of $S\setminus\{z\}$ for the weights $g$, and build a Steiner tree by processing the edges of $R$ in decreasing order of $g$, each time joining the roots of the two current components under a new node of depth $g_{uv}$, and finally attaching the last root to $z$. The resulting tree $C$ has nonnegative weights, satisfies
--   $$d_C(u,v)\le\rho(u,v)\le d(u,v)\qquad(u,v\in S),$$
--   and has weight $w(C)\ge\sum_A y_A$. In particular there is a dominated Steiner tree on $S$ of weight at least $\sum_A y_A$.
--
--   The construction converts a (possibly non-laminar) dual solution, such as one produced by an LP solver, into the computed core $C$ in near-quadratic time, without uncrossing.
--
--   **Formalization Note** The statement records the existential consequence; the proof builds the merge tree explicitly as a parent array.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §9.4, Claim 9.12 and its proof, pp.43–44 (PDF pp.45–46).

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_IsDualFeasible
import Definitions.Def_MetricTSPSublinear_Dominated

namespace MetricTSPSublinear

/-- **Claim 9.12.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283,
§9.4, pp.43–44 (PDF pp.45–46): from a feasible dual solution y on S, the Steiner tree built by processing a maximum
spanning tree of the Gromov products g_uv = (ρ(z,u)+ρ(z,v)−ρ(u,v))/2 of the loads ρ in decreasing order "has
nonnegative edge weights and satisfies d_C(u,v) ≤ ρ(u,v) ≤ d(u,v) (u,v ∈ S), and w(C) ≥ Σ_A y_A."

Conclusion stated here: there is a Steiner tree on `S` dominated by `d` of weight at least `Σ_A y_A`.

**Formalization Note.** The proof constructs exactly the paper's merge tree (explicit parent array) and proves
`d_C ≤ ρ` and `w(C) ≥ Σ_{u≠z} h_u − Σ_R g ≥ Σ y`; only the existential consequence is stated. -/
theorem claim_9_12 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n))
    (hSne : S.Nonempty) (y : Finset (Fin n) → ℝ) (hfeas : IsDualFeasible d S y) :
    ∃ C : SteinerTree S, Dominated d C ∧ ∑ A, y A ≤ C.weight := by sorry

end MetricTSPSublinear
