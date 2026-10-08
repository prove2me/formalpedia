-- Prove2me | Theorems.Thm_HryniewiczCriterion_graphUnitary2_polar_roots
-- name    : HryniewiczCriterion.graphUnitary2_polar_roots
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T16:12:42.667285+00:00
-- url     : https://prove2.me/theorems/78ebbab6-c9db-4761-89f6-033ed816bbd8
-- title:
--   Eigenvalues of the graph unitary of $R(x)P$ in $\mathrm{Sp}(1)$
-- statement:
--   Let $P$ be a real symmetric positive definite $2\times2$ matrix with $\det P=1$, let $x\in\mathbb{R}$, and let $g=R(x)P\in SL(2,\mathbb{R})$ (every element of $SL(2,\mathbb{R})$ has this polar form). Put $\gamma=\arccos(2/\operatorname{tr}P)\in[0,\pi/2)$. Then the eigenvalues of the graph unitary $W(\Gamma_g)W(\Delta)^{-1}$ (Souriau map of the graph $\Gamma_g\subset(\mathbb{R}^2\oplus\mathbb{R}^2,-\omega_0\oplus\omega_0)$, $\Delta$ the diagonal) are
--   $$e^{i(x+\gamma)},\qquad e^{i(x-\gamma)},$$
--   counted with multiplicity. In particular the rotation part of $g$ is the mean of the two eigen-angles, and the half-gap $\gamma$ depends only on $\operatorname{tr}P$.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, the eigenvalue computation behind (3.45)–(3.46), p. 222; Souriau map as in Robbin–Salamon, The Maslov index for paths, Topology 32 (1993). Explicit formula; not a verbatim numbered assertion.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.graphUnitary2_polar_roots (x : ℝ) {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.PosDef)
    (hdet : P.det = 1) :
    (graphUnitary2 (rotationMatrix x * P)).charpoly.roots =
      {Complex.exp ((x + Real.arccos (2 / (P 0 0 + P 1 1))) * Complex.I),
        Complex.exp ((x - Real.arccos (2 / (P 0 0 + P 1 1))) * Complex.I)} := by sorry
