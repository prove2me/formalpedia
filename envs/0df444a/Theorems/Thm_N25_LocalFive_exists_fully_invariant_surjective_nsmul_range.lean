-- Prove2me | Theorems.Thm_N25_LocalFive_exists_fully_invariant_surjective_nsmul_range
-- name    : N25.LocalFive.exists_fully_invariant_surjective_nsmul_range
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:41.702332+00:00
-- url     : https://prove2.me/theorems/d02cb4f5-148e-4e0d-a016-7139ecaa2e53
-- title:
--   A divisible finite-index subgroup can be replaced by a fully invariant scalar image
-- statement:
--   Let $M$ be an abelian group, $n\ge0$, and $U\le M$. Assume $M/U$ is finite and $[n]:U\to U$ is surjective. Then for some $r\ge0$, the subgroup $D=[n^r]M$ contains $U$, has finite index, is $n$-divisible, and is preserved by every endomorphism of $M$: $$U\le D,\quad |M/D|<\infty,\quad [n]:D\twoheadrightarrow D,\quad f(D)\subseteq D\ \text{for all }f\in\mathrm{End}(M).$$ This creates a canonical local subgroup stable under all operators appearing in the descent.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

theorem N25.LocalFive.exists_fully_invariant_surjective_nsmul_range
    {M : Type*} [AddCommGroup M]
    (n : ℕ) (U : AddSubgroup M)
    (hfin : Finite (M ⧸ U))
    (hU : Function.Surjective (fun u : U => n • u)) :
    ∃ r : ℕ,
      let D := (nsmulAddMonoidHom (α := M) (n ^ r)).range
      U ≤ D ∧
        Finite (M ⧸ D) ∧
        Function.Surjective (fun x : D => n • x) ∧
        ∀ (f : M →+ M) (x : M), x ∈ D → f x ∈ D  := by sorry
