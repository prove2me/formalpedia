-- Prove2me | Theorems.Thm_N25_unitRelationClearedSeries25_coefficients_of_polynomial
-- name    : N25.unitRelationClearedSeries25_coefficients_of_polynomial
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:50:41.469066+00:00
-- url     : https://prove2.me/theorems/426b6775-a237-4e41-a8a6-1d6852614dc4
-- title:
--   Polynomial coefficient vanishing transfers to the cleared relation series
-- statement:
--   Let $N,t∈ℕ$ satisfy $N≤25t$. If the numerator polynomial $P_t(X)$ has $[X^n]P_t=0$ for every $n<N$, then the cleared relation series $S(q)$ satisfies $$[q^n]S(q)=0\quad\text{for every }n<N.$$ This converts the finite polynomial certificate into q-series coefficient vanishing.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open scoped BigOperators
open Polynomial
open N25

theorem N25.unitRelationClearedSeries25_coefficients_of_polynomial (N t : ℕ)
    (hNt : N ≤ 25*t)
    (hp : ∀ n : ℕ, n < N → (unitRelationNumeratorPolynomial25 t).coeff n = 0) :
    ∀ n : ℕ, n < N → PowerSeries.coeff n unitRelationClearedSeries25 = 0 := by sorry
