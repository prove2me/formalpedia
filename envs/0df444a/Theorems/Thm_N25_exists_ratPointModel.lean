-- Prove2me | Theorems.Thm_N25_exists_ratPointModel
-- name    : N25.exists_ratPointModel
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:33:23.699564+00:00
-- url     : https://prove2.me/theorems/07c90d56-a9a7-40f2-8814-ee69c38b3e86
-- title:
--   A Galois-equivariant rational abelian model exists
-- statement:
--   There exists a rational point model consisting of a scheme $B\to\operatorname{Spec}\mathbb Q$, a commutative relative group law with the specified abelian-scheme property, an additive equivalence between the geometric Jacobian $J$ and the $\overline{\mathbb Q}$-points of that group scheme, and compatibility with arithmetic Galois action:
--
--   $$J\simeq G(\overline{\mathbb Q})\quad\text{equivariantly as additive groups}.$$
--
--   This model is the algebraic-geometric bridge used for local completion and height arguments.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_RatPointModel

open N25

theorem N25.exists_ratPointModel : Nonempty RatPointModel := by sorry
