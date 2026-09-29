-- Prove2me | Theorems.Thm_JewellMRP_Discounted_optValue_tendsto_eq14
-- name    : JewellMRP.Discounted.optValue_tendsto_eq14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:03:07.164526+00:00
-- url     : https://prove2.me/theorems/ad7bc638-b022-4785-ac38-54b488f27006
-- title:
--   Eq. (14), p. 945 — the optimal $n$-step returns converge to the solution of the optimality equation
-- statement:
--   Let a Markov-renewal program be given and let $\alpha > 0$. Let $V_i(n,\alpha)$ be the optimal $n$-step returns of (6) with boundary rewards $V_i(0,\alpha)$. Then there is a vector $v$ with
--   $$
--   v_i = \max_z \Big\{\rho^z_i(\alpha) + \sum_{j} p^z_{ij}\,\tilde f^z_{ij}(\alpha)\, v_j\Big\} \qquad \text{for every } i,
--   $$
--   such that $V_i(n,\alpha) \to v_i$ as $n \to \infty$, for every state $i$ and for every choice of boundary rewards $V_i(0,\alpha)$.
--
--   This is the limiting form (14) of the recursion (6): the limit exists, does not depend on the boundary rewards, and solves the optimality equation of the infinite-step problem.
--
--   **Formalization Note** The page prints $v_i(\alpha)$ inside the sum over $j$ in (14); this is a misprint for $v_j(\alpha)$, as (6), (15) and Fig. 1 show, and the corrected form is stated. The existence of the limit is a conclusion; the vector $v$ is chosen before the boundary rewards, which expresses that the limit does not depend on them.
-- source:
--   Jewell, Markov-Renewal Programming. I: Formulation, Finite Return Models, Operations Research 11(6), 1963, p. 945, Eq. (14) (misprint v_i for v_j under the sum corrected)

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

/-- Eq. (14), p. 945: for `α > 0` the optimal `n`-step returns `V_i(n, α)` of (6) converge,
as `n → ∞`, to a limit that does not depend on the boundary rewards and solves
`v_i = max_z [ρ^z_i(α) + Σ_j p^z_{ij} f̃^z_{ij}(α) v_j]`. -/
theorem optValue_tendsto_eq14 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    ∃ v : S → ℝ, (∀ i, v i = maxTest M α v i) ∧
      ∀ V0 : S → ℝ, Tendsto (optValue M α V0) atTop (𝓝 v) := by sorry

end JewellMRP.Discounted
