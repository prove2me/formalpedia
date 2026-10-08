-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_revisedDual_existsUnique_optimum
-- name    : KellyLossNetworks.RevisedDual.revisedDual_existsUnique_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:09:02.072105+00:00
-- url     : https://prove2.me/theorems/49babcab-7466-4c17-9e25-f15d9c5054b4
-- title:
--   §3.1, p. 338 — the revised dual problem (3.5) has a unique minimum
-- statement:
--   Consider a loss network with route rates $\nu_r>0$, link capacities $C_j\ge1$ and incidence matrix $A=(A_{jr})$ with entries in $\mathbb Z_+$. Then the revised dual problem
--   $$\text{minimize}\quad\sum_r\nu_r\exp\Big(-\sum_jy_jA_{jr}\Big)+\sum_j\int_0^{y_j}U(z,C_j)\,dz\qquad\text{subject to }y\ge0 \tag{3.5}$$
--   has exactly one optimum $y\ge0$.
--
--   The optimum $y$ is the vector through which Theorem 3.7 expresses the Erlang fixed point.
--
--   **Formalization Note** The paper deduces "a unique minimum" from strict convexity. Strict convexity gives at most one minimizer; this statement also asserts that a minimizer exists.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 338, §3.1, the paragraph after (3.5)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyLossNetworks_RevisedDual_Problem

namespace KellyLossNetworks.RevisedDual

/-- **The revised dual problem (3.5) has a unique minimum.** If `ν_r > 0` for every route and
`C_j ≥ 1` for every link, exactly one `y ≥ 0` minimizes the objective of (3.5) over `y ≥ 0`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, the paragraph after (3.5) (unnumbered).

**Formalization Note.** The paper infers "a unique minimum" from strict convexity, which gives at
most one minimizer; the existence half is part of this statement. -/
theorem revisedDual_existsUnique_optimum {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃! y : Fin J → ℝ, IsRevisedDualOptimum A ν C y := by sorry

end KellyLossNetworks.RevisedDual
