-- Prove2me | Theorems.Thm_Maldacena2003_shapeF_mem_Icc
-- name    : Maldacena2003.shapeF_mem_Icc
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:53:29.111767+00:00
-- url     : https://prove2.me/theorems/82dcc24d-1571-47b2-875e-94cb2a3b8acb
-- title:
--   Eq. (4.9): the shape function satisfies $0\le f(k)\le\frac56$
-- statement:
--   Let $(k_1,k_2,k_3)$ be a momentum triangle with positive sides, i.e. $k_i>0$ and each $k_i$ is at most the sum of the other two. Let
--   $$f(k) = \frac{\frac12\sum_ik_i^3+\frac12\sum_{i\neq j}k_ik_j^2+4\frac{\sum_{i>j}k_i^2k_j^2}{k_t}}{\sum_ik_i^3}-2$$
--   be the shape function of eq. (4.9). Then
--   $$0\le f(k)\le\frac56 .$$
--
--   This is the range statement of (4.9). Together with the tilt formula for $f_{NL}$, it bounds the size of the three-scalar non-Gaussianity of single-field slow-roll inflation in terms of $n_s$ and $n_t$ for every triangle shape.
--
--   **Formalization Note** The triangle condition is essential: outside the triangle region $f$ can be negative (e.g. $f(1,1,10)<0$).
-- source:
--   J. Maldacena, Non-Gaussian features of primordial fluctuations in single field inflationary models, JHEP 05 (2003) 013, https://doi.org/10.1088/1126-6708/2003/05/013 (arXiv:astro-ph/0210603), p. 18, sentence after eq. (4.9)

import Mathlib
import Definitions.Def_Maldacena2003_InflationDefs
open Filter Topology

namespace Maldacena2003

theorem shapeF_mem_Icc (k₁ k₂ k₃ : ℝ) (hk : IsMomentumTriangle k₁ k₂ k₃) :
    0 ≤ shapeF k₁ k₂ k₃ ∧ shapeF k₁ k₂ k₃ ≤ 5 / 6 := by sorry

end Maldacena2003
