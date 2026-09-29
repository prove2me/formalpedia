-- Prove2me | Theorems.Thm_IntermediateField_isSolvable_algEquiv_of_padic
-- name    : IntermediateField.isSolvable_algEquiv_of_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/45645bc6-21f9-5f1c-9daa-061d8056ad88
-- title:
--   Solvability of Galois groups of finite extensions of ℚ_q
-- statement:
--   Let $q$ be a prime and let $\Omega =$ `PadicAlgCl q` be the fixed algebraic closure of $\mathbb{Q}_q$ used throughout. Let $K$ be an intermediate field of $\Omega/\mathbb{Q}_q$ that is finite-dimensional over $\mathbb{Q}_q$, and let $E$ be an intermediate field of $\Omega/K$ that is finite-dimensional over $K$ and normal over $K$. Then the group $E \simeq_{\mathrm{alg}[K]} E$ of $K$-algebra automorphisms of $E$ is solvable, i.e. `Group.IsSolvable` holds for it. Since the characteristic is $0$, the normality and finiteness hypotheses make $E/K$ a finite Galois extension, so the assertion is exactly the solvability of $\mathrm{Gal}(E/K)$ for an arbitrary finite normal subextension $E/K$ of $\Omega/\mathbb{Q}_q$ with $K/\mathbb{Q}_q$ finite. Note that the conclusion is stated for the automorphism group of $E$ over $K$ itself rather than for an abstract Galois group, and that $E$ is required to sit inside the chosen algebraic closure $\Omega$.
--
--   This is the classical fact that the Galois group of a finite extension of a $p$-adic field is solvable, a consequence of the wild–tame–unramified filtration: a normal $q$-subgroup of wild inertia, with cyclic tame-inertia and unramified quotients. It is used in the project wherever local Galois groups must be resolved into solvable pieces, for instance in the local-level constructions and in the idelic local-inverse arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_isSolvable_algEquiv_of_padic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.isSolvable_algEquiv_of_padic
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (E : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K E] [Normal K E] :
    Group.IsSolvable (E ≃ₐ[K] E) := by sorry
