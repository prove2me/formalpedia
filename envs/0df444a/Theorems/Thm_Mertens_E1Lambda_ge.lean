-- Prove2me | Theorems.Thm_Mertens_E1Lambda_ge
-- name    : Mertens.E1Lambda.ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:26:05.852919+00:00
-- url     : https://prove2.me/theorems/15385716-9859-405a-b235-710616a9a3d3
-- title:
--   Lower bound $E_{1\Lambda}(x) \ge -2$ for the Mertens remainder
-- statement:
--   Define the remainder term in Mertens' first theorem (von Mangoldt form) by
--   $$E_{1\Lambda}(x) \;=\; \sum_{1 \le d \le \lfloor x \rfloor} \frac{\Lambda(d)}{d} \;-\; \log x,$$
--   where $\Lambda$ is the von Mangoldt function and the sum runs over the integers $d$ with $0 < d \le \lfloor x \rfloor$.
--
--   **Statement.** For every real $x \ge 1$,
--   $$E_{1\Lambda}(x) \ge -2.$$
--
--   Together with the companion upper bound `Mertens.E1Lambda.le`, this makes the Mertens estimate $\sum_{d \le x} \Lambda(d)/d = \log x + O(1)$ fully explicit. In the project (module `Zeta23.FromPNTPlus.Mertens`, ported from PrimeNumberTheoremAnd) it is consumed by `Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit`, an explicit Chebyshev-type evaluation of $\sum \Lambda(n)^2/n$-type sums used in the mollified second-moment computation.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/Mertens.lean#L154-L170

import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens

open Mertens
open Real Finset Filter Asymptotics
open ArithmeticFunction hiding log

theorem Mertens.E1Lambda.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by sorry
