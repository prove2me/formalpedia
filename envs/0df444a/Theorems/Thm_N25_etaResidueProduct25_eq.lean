-- Prove2me | Theorems.Thm_N25_etaResidueProduct25_eq
-- name    : N25.etaResidueProduct25_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:31:16.644573+00:00
-- url     : https://prove2.me/theorems/43659e96-eb9f-4cec-a5b5-ff3cc5f2db1d
-- title:
--   The residue-filtered Euler product equals the indexed two-factor product
-- statement:
--   Let $0<g<25$ and let $q\in\mathbb C$ satisfy $|q|<1$. Filtering positive exponents by the residue classes $g$ and $25-g$ gives the same convergent product as indexing the two classes directly:
--
--   $$\prod_{k\ge0}A_k(q)B_k(q)=\prod_{n\ge0}(1-q^{25n+g})(1-q^{25(n+1)-g}),$$
--
--    where $A_k(q)=1-q^{k+1}$ when $k+1\equiv g\pmod{25}$ and $1$ otherwise, and $B_k$ is defined similarly for $25-g$. This reindexing links the formal residue series to the analytic product.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open scoped BigOperators
open Polynomial

theorem N25.etaResidueProduct25_eq (g : ℕ) (hg : 0 < g) (hg25 : g < 25)
    (q : ℂ) (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (if (k + 1) % 25 = g then 1 - q ^ (k + 1) else 1) *
      (if (k + 1) % 25 = 25 - g then 1 - q ^ (k + 1) else 1)) =
    ∏' n : ℕ, (1 - q ^ (25 * n + g)) * (1 - q ^ (25 * (n + 1) - g)) := by sorry
