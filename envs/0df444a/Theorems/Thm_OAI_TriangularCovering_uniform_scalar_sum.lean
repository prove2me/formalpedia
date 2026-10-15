-- Prove2me | Theorems.Thm_OAI_TriangularCovering_uniform_scalar_sum
-- name    : OAI.TriangularCovering.uniform_scalar_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T19:00:37.178996+00:00
-- url     : https://prove2.me/theorems/ca101fd2-3dce-439c-bd33-3517459ab77b
-- title:
--   Mesh sum of normalized cylinder areas equals $\tfrac12-\tfrac{13}{6000}\varepsilon^2$ up to $14\varepsilon^4$
-- statement:
--   Fix the constant $\eta=\tfrac{1}{1000}$ and define, for real numbers $a,b,q,\varepsilon$,
--   $$
--   d(q)=\frac{q^2(1+q^2)}{16},\qquad \alpha(a,b)=\frac{1+ab}{4},\qquad \beta(a,b)=\frac{a+b}{4},\qquad \sigma(a,b)=\alpha(a,b)^2+2\beta(a,b)^2,
--   $$
--   $$
--   \kappa(a,b)=\eta+\max\bigl(d(a),d(b)\bigr),\qquad T_\varepsilon(a,b)=\frac{(b-a)\bigl(\tfrac12+\varepsilon^2\kappa(a,b)\bigr)^2}{\sqrt{1+\varepsilon^2\sigma(a,b)}} .
--   $$
--   For a positive integer $N$ let $h_N=2/N$ and let $m_j=-1+j\,h_N$ $(0\le j\le N)$ be the uniform mesh of $[-1,1]$ with $N$ intervals.
--
--   Let $\varepsilon\in\mathbb{R}$ and $N\ge 1$ satisfy $|\varepsilon|\le 1$ and $h_N=2/N\le\varepsilon^2$. Then
--
--   $$
--   \left|\ \sum_{j=0}^{N-1}T_\varepsilon(m_j,m_{j+1})-\Bigl(\frac12-\frac{13}{6000}\,\varepsilon^2\Bigr)\right|\le 14\,\varepsilon^4 .
--   $$
--
--   The point is that the error is of fourth order in $\varepsilon$ with the absolute constant $14$, independent of the number $N$ of intervals as long as the mesh is fine compared with $\varepsilon^2$. In the covering of the regular tetrahedron by triangular cylinders, $T_\varepsilon(m_j,m_{j+1})$ is the combined base area, divided by $H=\sqrt2$, of the two cylinders attached to the $j$-th mesh interval, and the construction uses $N=\lceil 2/\varepsilon^2\rceil$, which satisfies $2/N\le\varepsilon^2$. The theorem therefore yields the expansion $\tfrac12-\tfrac{13}{6000}\varepsilon^2+O(\varepsilon^4)$ for the normalized total base area of that covering.
--
--   **Formalization Note** In Lean, $T_\varepsilon(a,b)$ is `normalizedTerm ε a b`, $\kappa$ is `cutoffCoeff`, $\sigma$ is `speedSq`, $\alpha,\beta,d,\eta$ are `alpha`, `beta`, `d`, `η`, $h_N$ is `step N` and $m_j$ is `mesh N j`. The sum runs over `j : Fin N`, and $m_{j+1}$ is `mesh N (j+1)` with $j+1$ computed as a natural number (no wrap-around). The hypotheses force $\varepsilon\ne 0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Asymptotics.lean#L301-L321

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron
import Definitions.Def_OAI_Geometry_TriangularCovering_Shadows
import Definitions.Def_OAI_Geometry_TriangularCovering_Asymptotics

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.uniform_scalar_sum {ε : ℝ} {N : ℕ} (he : |ε| ≤ 1) (hN : 0 < N)
    (hstep : step N ≤ ε^2) :
    |(∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2-(13/6000:ℝ)*ε^2)| ≤ 14*ε^4 := by sorry
