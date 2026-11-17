-- Prove2me | Theorems.Thm_N25_etaResidueSeries25_coeff
-- name    : N25.etaResidueSeries25_coeff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:08.255346+00:00
-- url     : https://prove2.me/theorems/3b2ff432-d6fc-4106-8baf-220455ef4e09
-- title:
--   Each coefficient is determined by a finite residue-filtered product
-- statement:
--   Let $0<g<25$ and $n\ge0$. The coefficient of degree $n$ in the residue power series $R_g$ equals the coefficient of degree $n$ in the product of the first $n$ residue-filtered polynomial factors:
--
--   $$[X^n]R_g=[X^n]\prod_{0\le k<n}A_k(X)B_k(X),$$
--
--    with $A_k(X)=1-X^{k+1}$ precisely when $k+1\equiv g\pmod{25}$ and $B_k(X)=1-X^{k+1}$ precisely when $k+1\equiv25-g\pmod{25}$. This reduces each coefficient to a finite computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open scoped BigOperators
open Polynomial
open N25

theorem N25.etaResidueSeries25_coeff (g : ℕ) (hg : 0 < g) (hg25 : g < 25) (n : ℕ) :
    PowerSeries.coeff n (etaResidueSeries25 g) =
      (∏ k ∈ Finset.range n,
        ((if (k + 1) % 25 = g then (1 - X ^ (k + 1) : ℤ[X]) else 1) *
          (if (k + 1) % 25 = 25 - g then (1 - X ^ (k + 1) : ℤ[X]) else 1))).coeff n := by sorry
