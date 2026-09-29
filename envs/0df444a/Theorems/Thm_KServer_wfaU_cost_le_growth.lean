-- Prove2me | Theorems.Thm_KServer_wfaU_cost_le_growth
-- name    : KServer.wfaU_cost_le_growth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T05:13:07.941298+00:00
-- url     : https://prove2.me/theorems/ac71e0e1-fd3f-4d88-af4d-e5ceaac17b79
-- title:
--   The classical WFA's cost plus OPT is at most the total extended cost
-- statement:
--   Let $\mathrm{WFA}$ be the classical Work Function Algorithm --- the one whose step minimises movement cost plus the work function $w$ of the **unlabelled** configuration --- running from the initial configuration $C_0$ on the request sequence $\sigma = r_1 \dots r_n$, and write $w_t$ for the work function of the first $t$ requests. Suppose $u_t$ is a budget dominating the $t$-th **extended cost**:
--
--   $$w_{t+1}(X) \;\le\; w_t(X) + u_t \qquad \text{for every configuration } X.$$
--
--   Then
--
--   $$\mathrm{cost}(\mathrm{WFA}, \sigma) \;+\; \mathrm{OPT}(\sigma) \;\le\; \sum_{t<n} u_t.$$
--
--   ## Role
--
--   This is the entry point of every potential-function analysis of the Work Function Algorithm --- Lemma 2 of Bein, Chrobak and Larmore, and the standard first step in Chrobak--Larmore, Koutsoupias's survey, and Coester--Koutsoupias. It converts competitive analysis of the algorithm into a statement about the work function alone: if the total extended cost is at most $(c+1)\,\mathrm{OPT}$ plus a constant, then $\mathrm{WFA}$ is $c$-competitive, since $\mathrm{OPT}$ appears on the left with coefficient one. In particular the Coester--Koutsoupias bound of $(k+1)\,\mathrm{OPT} + c_M$ for the total extended cost on trees yields $k$-competitiveness there, which for $k=3$ is their Theorem 23.
--
--   The proof is the telescoping argument: the algorithm's defining minimality makes each of its moves *lazy* for the new work function --- the move costs exactly the difference between the new work function at the old and at the new configuration --- after which the cost sums to the work-function increments along the trajectory plus a telescoped term, bounded below by $\mathrm{OPT}$ at the final configuration.
--
--   It is essential here that the algorithm and the budget hypothesis refer to the **same** work function, the unlabelled one. For the variant of the algorithm built from the labelled work function this lemma holds only with labelled increments on the right, and the corresponding total is strictly larger --- on trees it exceeds $4\,\mathrm{OPT}$ by a linearly growing margin, which is why that variant escapes the classical analysis.
--
--   ## Formalization note
--
--   `WFAU` is the classical algorithm packaged as a deterministic online algorithm; ties in its step are broken by a fixed arbitrary choice, and the lemma holds regardless, because laziness of the step is a consequence of minimality alone. `workFnU` is the unlabelled work function, `offlineCost` the optimal offline cost, and `cost` the sum of labelled movement costs between successive configurations --- which for this algorithm is the matching cost, since its minimisation selects an optimally labelled target.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, 'The 3-server problem in the plane', Theoretical Computer Science 289 (2002), Lemma 2; E. Koutsoupias, 'The k-server problem', Computer Science Review 3 (2009), Section 3; the same telescoping step opens the potential argument of C. Coester, E. Koutsoupias, ICALP 2021.

import Mathlib
import Definitions.Def_KServer_wfaU

namespace KServer

theorem wfaU_cost_le_growth (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (σ : List M) (u : ℕ → ℝ)
    (hu : ∀ t : ℕ, t < σ.length → ∀ X : Config k M,
      workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) :
    (WFAU hk C₀).cost σ + offlineCost C₀ σ ≤ ∑ t ∈ Finset.range σ.length, u t := by sorry

end KServer
