-- Prove2me | Theorems.Thm_N25_etaResidueSeries25_hasSum
-- name    : N25.etaResidueSeries25_hasSum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:07.463028+00:00
-- url     : https://prove2.me/theorems/fc525cc9-f3d7-47c5-b67f-c0a652c15386
-- title:
--   The eta residue power series sums to its Euler product
-- statement:
--   Let $0<g<25$, let $q\in\mathbb C$ with $|q|<1$, and let $a_n=[X^n]R_g$. Then
--
--   $$\sum_{n\ge0}a_nq^n=\prod_{k\ge0}A_k(q)B_k(q),$$
--
--    where the two factors select exponents congruent to $g$ and $25-g$ modulo $25$. This establishes analytic convergence of the formal residue series.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open Polynomial
open scoped BigOperators
open N25

theorem N25.etaResidueSeries25_hasSum
    (g : ℕ) (hg : 0 < g) (hg25 : g < 25)
    (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ =>
      ((PowerSeries.coeff n (etaResidueSeries25 g) : ℤ) : ℂ) * q ^ n)
      (∏' k : ℕ,
        (if (k + 1) % 25 = g then 1 - q ^ (k + 1) else 1) *
        (if (k + 1) % 25 = 25 - g then 1 - q ^ (k + 1) else 1)) := by sorry
