-- Prove2me | Theorems.Thm_OAI_Problem356_CoulombEstimates_coulombCost_le_add_of_separated
-- name    : OAI.Problem356.CoulombEstimates.coulombCost_le_add_of_separated
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:43:12.674561+00:00
-- url     : https://prove2.me/theorems/31e4d272-c7b5-4aec-8cd5-9a7eac9c6cd7
-- title:
--   One-sided oscillation bound for the extended Coulomb cost
-- statement:
--   Work in $\mathbb{R}^3$ with the three-body Coulomb cost $c(x,y,z)=|x-y|^{-1}+|x-z|^{-1}+|y-z|^{-1}\in[0,\infty]$. A three-coupling of $\mu$ is a probability measure on triples with all three marginals $\mu$; the Kantorovich value is the infimum of $\int c\,d\pi$ over three-couplings, and a Monge optimizer is a pair of $\mu$-preserving maps $(T_2,T_3)$ whose graph coupling attains it. A smooth compact probability density $\rho$ is nonnegative, smooth, compactly supported, with smooth compactly supported square root and $\int\rho=1$. Let $(x,y,z)$ and $(x',y',z')$ be $\eta$-separated triples in $\mathbb{R}^3$ with $\eta>0$ and $|x-x'|,|y-y'|,|z-z'|\le\delta$. Then
--   $$
--   c(x,y,z)\le c(x',y',z')+\frac{6\delta}{\eta^2} .
--   $$
--
--   This extended-valued version is suitable for lower integrals of the cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CoulombTransport/CoulombEstimates.lean#L126-L146

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates

open OAI OAI.Problem356 OAI.Problem356.CoulombEstimates
universe uE uA
open MeasureTheory
open scoped ENNReal

theorem OAI.Problem356.CoulombEstimates.coulombCost_le_add_of_separated {x y z x' y' z' : E3} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    coulombCost (x, (y, z)) ≤ coulombCost (x', (y', z')) +
      ENNReal.ofReal ((6 * delta) / eta ^ 2) := by sorry
