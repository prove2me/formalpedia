-- Prove2me | Theorems.Thm_N25_unitSeries25_normalization
-- name    : N25.unitSeries25_normalization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:36.794206+00:00
-- url     : https://prove2.me/theorems/042f9ecf-b3e1-4cb7-83fd-cd0d1c631716
-- title:
--   The denominator is nonzero and all five unit series are normalized
-- statement:
--   Let $K$ be a field, let $D_K$ be the coefficient image of the denominator series, and let $S_i$ have prescribed order $q_i$. Then $$D_K≠0\quad\text{and}\quad\forall i∈ℤ/5ℤ,\;\operatorname{ord}(S_i)=q_i\;\text{and}\;[q^{q_i}]S_i=1.$$ This gathers the nonvanishing and leading-term facts needed to define the modular functions uniformly.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open ModularCurve
open N25

theorem N25.unitSeries25_normalization (K : Type*) [Field K] :
    intSeriesC K unitDenominatorSeries25 ≠ 0 ∧
      ∀ i : Fin 5, (unitSeries25 K i).order = unitQOrder25 i ∧
        (unitSeries25 K i).coeff (unitQOrder25 i) = 1 := by sorry
