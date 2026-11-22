-- Prove2me | Theorems.Thm_NoHair_kerrNewman_exterior_globallyHyperbolic
-- name    : NoHair.kerrNewman_exterior_globallyHyperbolic
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T19:45:02.074987+00:00
-- url     : https://prove2.me/theorems/5a3350c3-9209-4a9e-8edc-18d3a769496d
-- title:
--   Global hyperbolicity of the open Kerr–Newman exterior
-- statement:
--   Let $m>0$, $a^2+e^2\le m^2$, and let $T$ be a continuous timelike orientation of the Kerr–Newman spacetime $\{r>0\}$. The open region $D=\{r>r_+\}$ is globally hyperbolic for the restricted metric. It contains no closed future causal curve, and its intrinsic causal diamonds satisfy
--
--   $$J^+_D(p)\cap J^-_D(q)\text{ is compact for all }p,q\in D.$$
--
--   Both the causal relations and the curves in this statement are restricted to the exterior. Its formulation permits either time orientation and includes a degenerate outer horizon.
-- source:
--   W. Hasse and V. Perlick, A Morse-theoretical analysis of gravitational lensing by a Kerr-Newman black hole, https://arxiv.org/abs/gr-qc/0511135, §III, p. 4, Eqs. (8)–(12) and the paragraph identifying the Boyer–Lindquist time slices as Cauchy surfaces; Prove2Me, NoHair.kerrNewman_isStationaryBlackHole, https://prove2.me/theorems/d4aa60f2-99c7-4a52-9c28-6ba24b2ddbac, exterior global hyperbolicity.

import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open NoHair Set

theorem NoHair.kerrNewman_exterior_globallyHyperbolic (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    IsGloballyHyperbolicOn (kerrNewmanMetricField m a e) T
      ((Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e) := by sorry
