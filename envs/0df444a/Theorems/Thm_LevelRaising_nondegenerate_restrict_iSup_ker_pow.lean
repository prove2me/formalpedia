-- Prove2me | Theorems.Thm_LevelRaising_nondegenerate_restrict_iSup_ker_pow
-- name    : LevelRaising.nondegenerate_restrict_iSup_ker_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/965a4876-332c-5d59-9e63-742ec0f200c4
-- title:
--   Non-degeneracy restricts to the generalised kernel of a self-adjoint endomorphism
-- statement:
--   Let $F$ be a field and $V$ a finite-dimensional $F$-vector space, and let $B : V \times V \to F$ be an $F$-bilinear form on $V$. Assume $B$ is non-degenerate in each slot separately, in the pointwise sense: every $x$ with $B(x,y)=0$ for all $y$ is zero, and every $y$ with $B(x,y)=0$ for all $x$ is zero. Let $g$ be an $F$-linear endomorphism of $V$ which is self-adjoint for $B$, i.e. $B(gx,y)=B(x,gy)$ for all $x,y \in V$. Write $K := \bigsqcup_{n \in \mathbb{N}} \ker(g^n)$ for the supremum in the lattice of submodules of the kernels of the powers of $g$ (the generalised kernel of $g$). The conclusion is the conjunction of two statements: first, every $x \in K$ such that $B(x,y)=0$ for all $y \in K$ is zero; second, every $y \in K$ such that $B(x,y)=0$ for all $x \in K$ is zero. Thus $B$ restricted to $K$ is again non-degenerate in both slots, stated pointwise rather than via `LinearMap.BilinForm` restriction and `Nondegenerate`.
--
--   This is the linear-algebra fact that a non-degenerate bilinear form restricts non-degenerately to the Fitting zero-component (generalised kernel) of an endomorphism that is self-adjoint for the form; applied with $g = T - a$ for a Hecke operator $T$ it isolates one primary component of a Hecke module without destroying the duality. It is used in the level-raising part of the development, in [`LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime`](thm.html#LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LevelRaising_nondegenerate_restrict_iSup_ker_pow.lean

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LevelRaising.nondegenerate_restrict_iSup_ker_pow
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V)
    (hBl : ∀ x, (∀ y, B x y = 0) → x = 0) (hBr : ∀ y, (∀ x, B x y = 0) → y = 0)
    (g : Module.End F V) (hadj : ∀ x y, B (g x) y = B x (g y)) :
    (∀ x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n),
        (∀ y ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), B x y = 0) → x = 0) ∧
      (∀ y ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n),
        (∀ x ∈ ⨆ n : ℕ, LinearMap.ker (g ^ n), B x y = 0) → y = 0) := by sorry
