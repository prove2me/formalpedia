-- Prove2me | Theorems.Thm_N25_LocalFive_finite_quotient_and_surjective_nsmul_map
-- name    : N25.LocalFive.finite_quotient_and_surjective_nsmul_map
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:42.063777+00:00
-- url     : https://prove2.me/theorems/0ad4c902-7e1d-4615-86b6-d6803fbea229
-- title:
--   Finite-index divisibility descends along a surjection
-- statement:
--   Let $e:A\to B$ be a surjective homomorphism of abelian groups, let $n\ge0$, and let $U\le A$. If $A/U$ is finite and $[n]:U\to U$ is surjective, then the image subgroup $e(U)\le B$ satisfies $$|B/e(U)|<\infty,\qquad [n]:e(U)\twoheadrightarrow e(U).$$ This carries divisibility from integral model points to the local points they cover.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

theorem N25.LocalFive.finite_quotient_and_surjective_nsmul_map
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A →+ B) (he : Function.Surjective e)
    (n : ℕ) (U : AddSubgroup A)
    (hfin : Finite (A ⧸ U))
    (hU : Function.Surjective (fun u : U => n • u)) :
    Finite (B ⧸ U.map e) ∧
      Function.Surjective (fun u : U.map e => n • u)  := by sorry
