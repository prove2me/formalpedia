-- Prove2me | Theorems.Thm_NoHair_kerrNewman_regularTensors
-- name    : NoHair.kerrNewman_regularTensors
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T19:45:07.850935+00:00
-- url     : https://prove2.me/theorems/68f76ba9-21a0-4e2d-b77e-ee28df7c13f3
-- title:
--   Smooth Kerr–Newman tensor fields and Lorentzian signature on $r>0$
-- statement:
--   Let $m,a,e$ be real, let $r$ be the Kerr–Schild radius, and put $U_a=\{r>0\}$. The Kerr–Newman metric $g$ and electromagnetic field $F=dA$ restrict to smooth bilinear tensor fields on $U_a$, and the metric has Lorentzian signature at every point:
--
--   $$g,F\in C^\infty(U_a),\qquad \operatorname{sig}(g)=(-,+,+,+).$$
--
--   Smoothness means smoothness of the components in every chart of the induced atlas. These local assertions hold for every choice of the mass, angular momentum parameter and charge.
-- source:
--   T. Adamo and E. T. Newman, The Kerr–Newman metric: A Review, https://arxiv.org/abs/1410.6626v2, §2.3, Eq. (2.36), and §3.1, Eqs. (3.15)–(3.16); Prove2Me, NoHair.kerrNewman_isStationaryBlackHole, https://prove2.me/theorems/d4aa60f2-99c7-4a52-9c28-6ba24b2ddbac, local tensor hypotheses.

import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open NoHair Set

theorem NoHair.kerrNewman_regularTensors (m a e : ℝ) :
    IsLorentzian (kerrNewmanMetricField m a e) ∧
    IsSmoothBilinField (kerrNewmanMetricField m a e) ∧
    IsSmoothBilinField (kerrNewmanFieldField a e) := by sorry
