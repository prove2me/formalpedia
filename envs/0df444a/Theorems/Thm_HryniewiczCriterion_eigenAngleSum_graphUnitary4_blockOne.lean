-- Prove2me | Theorems.Thm_HryniewiczCriterion_eigenAngleSum_graphUnitary4_blockOne
-- name    : HryniewiczCriterion.eigenAngleSum_graphUnitary4_blockOne
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:36:33.458988+00:00
-- url     : https://prove2.me/theorems/0325d6b5-e0d9-4ff7-b91d-10ddb949097c
-- title:
--   Eigen-angle sum of the graph unitary of $\mathrm{diag}(I_2,g)$
-- statement:
--   For every real $2\times2$ matrix $g$,
--   $$\sum_{\lambda\in\operatorname{spec}V_4(\operatorname{diag}(I_2,g))}\operatorname{ang}(\lambda)\;=\;4\pi+\sum_{\mu\in\operatorname{spec}V_2(g)}\operatorname{ang}(\mu),$$
--   with eigenvalues counted with algebraic multiplicity and $\operatorname{ang}\in(0,2\pi]$, $\operatorname{ang}(1)=2\pi$. Here $V_4$ and $V_2$ are `graphUnitary4` and `graphUnitary2`.
--
--   Proof idea: after permuting rows to $(0,2,1,3)$ and columns to $(0,1,2,3)$, `graphBasis4 (blockOne g)` is block diagonal with blocks `graphBasis2 1` and `graphBasis2 g`. So $V_4(\operatorname{diag}(I_2,g))$ is conjugate to $\operatorname{diag}(V_2(1),V_2(g))=\operatorname{diag}(I_2,V_2(g))$, and the charpoly factors as $(X-1)^2\,\chi_{V_2(g)}$. If `graphBasis2 g` is singular, both unitaries are $0$ by the convention $0^{-1}=0$. Then both sides equal $8\pi$, since $\operatorname{ang}(0)=2\pi$.
-- source:
--   Block structure of the Souriau map on a symplectic direct sum; used for the kernel count (3.42) in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, proof of Theorem 3.4, p. 221.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff ComplexOrder

theorem HryniewiczCriterion.eigenAngleSum_graphUnitary4_blockOne (g : Matrix (Fin 2) (Fin 2) ℝ) :
    eigenAngleSum (graphUnitary4 (blockOne g)) = 4 * Real.pi + eigenAngleSum (graphUnitary2 g) := by sorry
