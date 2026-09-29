-- Prove2me | Theorems.Thm_Mertens_E1Lambda_le
-- name    : Mertens.E1Lambda.le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:26:11.957025+00:00
-- url     : https://prove2.me/theorems/ab57a677-292d-47f9-84be-afe1577e0e72
-- title:
--   Upper bound $E_{1\Lambda}(x) \le \log 4 + 4$ for the Mertens remainder
-- statement:
--   With the remainder term of Mertens' first theorem (von Mangoldt form) defined as
--   $$E_{1\Lambda}(x) \;=\; \sum_{1 \le d \le \lfloor x \rfloor} \frac{\Lambda(d)}{d} \;-\; \log x,$$
--   where $\Lambda$ is the von Mangoldt function and the sum runs over integers $d$ with $0 < d \le \lfloor x \rfloor$:
--
--   **Statement.** For every real $x \ge 1$,
--   $$E_{1\Lambda}(x) \le \log 4 + 4.$$
--
--   This is the explicit upper-bound half of Mertens' estimate $\sum_{d \le x} \Lambda(d)/d = \log x + O(1)$, with the absolute constant $\log 4 + 4$ spelled out. In the module `Zeta23.FromPNTPlus.Mertens` it is consumed, together with the matching lower bound `Mertens.E1Lambda.ge`, by `Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit` in the Chebyshev-type estimates feeding the mollified second-moment argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/Mertens.lean#L173-L194

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

theorem Mertens.E1Lambda.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by sorry
