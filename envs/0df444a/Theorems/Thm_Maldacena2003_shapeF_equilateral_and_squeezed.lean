-- Prove2me | Theorems.Thm_Maldacena2003_shapeF_equilateral_and_squeezed
-- name    : Maldacena2003.shapeF_equilateral_and_squeezed
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:53:58.077644+00:00
-- url     : https://prove2.me/theorems/04c9dc58-45c4-4080-acec-e13691b83366
-- title:
--   Eq. (4.9): $f = \frac56$ for equilateral triangles and $f\to0$ in the squeezed limit
-- statement:
--   Let $k>0$ and let $f$ be the shape function of eq. (4.9).
--
--   1. For the equilateral triangle, $f(k,k,k)=\frac56$.
--   2. As $(k_2,k_3)\to(k,0)$ through pairs for which $(k,k_2,k_3)$ is a momentum triangle with positive sides, $f(k,k_2,k_3)\to0$.
--
--   These are the two extreme values of $f$ described after (4.9). Since $f$ is homogeneous of degree zero, the second item is the statement that $f\to0$ "when two sides become much larger than the third".
--
--   **Formalization Note** The squeezed limit is a limit in $\mathbb R^2$ within the momentum-triangle set.
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), p. 18, sentence after eq. (4.9)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem shapeF_equilateral_and_squeezed (k : ℝ) (hk : 0 < k) :
    shapeF k k k = 5 / 6 ∧
      Tendsto (fun p : ℝ × ℝ => shapeF k p.1 p.2)
        (𝓝[{p : ℝ × ℝ | IsMomentumTriangle k p.1 p.2}] (k, 0)) (𝓝 0) := by sorry

end Maldacena2003
