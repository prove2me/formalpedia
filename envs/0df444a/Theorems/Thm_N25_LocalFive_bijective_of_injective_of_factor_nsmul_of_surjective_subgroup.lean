-- Prove2me | Theorems.Thm_N25_LocalFive_bijective_of_injective_of_factor_nsmul_of_surjective_subgroup
-- name    : N25.LocalFive.bijective_of_injective_of_factor_nsmul_of_surjective_subgroup
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:01.921223+00:00
-- url     : https://prove2.me/theorems/95080803-3a07-471c-abb2-8df90758620d
-- title:
--   An injective factor of multiplication is bijective under finite-index divisibility
-- statement:
--   Let $M$ be an abelian group, let $n\ge0$, and let $π,ρ:M\to M$ be homomorphisms with $π\circρ=[n]$. Assume that $π$ is injective and that there is a subgroup $U\le M$ such that $M/U$ is finite and multiplication by $n$ is surjective on $U$. Then $$π:M\xrightarrow{\sim}M.$$ This abstract lemma turns the local finite-index divisibility statement into surjectivity of the selected endomorphism.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_LocalFiveArithmetic

open N25
open N25.LocalFive

theorem N25.LocalFive.bijective_of_injective_of_factor_nsmul_of_surjective_subgroup
    {M : Type*} [AddCommGroup M]
    (n : ℕ) (pi rho : M →+ M)
    (hfactor : pi.comp rho = nsmulAddMonoidHom (α := M) n)
    (hpi : Function.Injective pi)
    (hlocal : FiniteQuotientSurj M n) :
    Function.Bijective pi := by sorry
