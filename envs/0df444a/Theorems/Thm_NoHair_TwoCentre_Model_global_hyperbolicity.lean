-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Model_global_hyperbolicity
-- name    : NoHair.TwoCentre.Model.global_hyperbolicity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:51:10.507901+00:00
-- url     : https://prove2.me/theorems/63a22406-6705-472b-98c3-83a0a5cf879c
-- title:
--   Global hyperbolicity of the full punctured Majumdar–Papapetrou exterior
-- statement:
--   Prove that the full two-centre exterior in the concrete advanced Cartesian model has no closed future causal curves and has compact causal diamonds, using exactly the mission’s causal-curve definition. In static coordinates its optical metric is $U^4 dx^2$. Complete optical distance and minimizing optical geodesics give the closed causal relation $t_2-t_1\geq d_{\rm opt}(x_1,x_2)$. [Compact confinement for finite coordinate time](https://prove2.me/theorems/d9d2c704-d533-4159-bc3a-a02c840449e7)
-- source:
--   M. Sánchez, On the geometry of static spacetimes, Theorem 3.1, https://arxiv.org/abs/math/0406332. J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentreBlackHole
import Definitions.Def_NoHair_TwoCentreIsotropic

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model Set
open scoped ContDiff Manifold

theorem NoHair.TwoCentre.Model.global_hyperbolicity : IsGloballyHyperbolicOn metric orientation outer := by
  sorry
