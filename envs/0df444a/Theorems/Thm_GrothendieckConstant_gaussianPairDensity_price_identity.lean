-- Prove2me | Theorems.Thm_GrothendieckConstant_gaussianPairDensity_price_identity
-- name    : GrothendieckConstant.gaussianPairDensity_price_identity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:58:04.496796+00:00
-- url     : https://prove2.me/theorems/bb4bfdfc-4dcc-425d-8a98-1b646de8d12b
-- title:
--   Price’s differential identity for the bivariate Gaussian density
-- statement:
--   For the centered bivariate normal density with unit marginal variances and correlation $|t|<1$, differentiation in $t$ equals mixed spatial differentiation in $x$ and $y$. This is the density identity behind Gaussian interpolation and Price differentiation in the estimates for the cubic–quintic Grothendieck scheme.
-- source:
--   Price’s theorem for the bivariate Gaussian density. The density is the one used in the cubic–quintic Grothendieck scheme, Saha et al., arXiv:2608.11158v2.

import Definitions.Def_KrivineSchemeDefs

namespace GrothendieckConstant

theorem gaussianPairDensity_price_identity (t x y : ℝ) (ht : |t| < 1) :
    deriv (fun s : ℝ => gaussianPairDensity 1 s ![x] ![y]) t =
      deriv (fun u : ℝ => deriv (fun v : ℝ => gaussianPairDensity 1 t ![u] ![v]) y) x := by sorry

end GrothendieckConstant
