-- Prove2me | Theorems.Thm_LinearMap_exists_injective_range_eq_ker_of_isTorsion
-- name    : LinearMap.exists_injective_range_eq_ker_of_isTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/94b1ac05-01c5-5b90-97eb-594f419b64c7
-- title:
--   Kernel of a map A^r → torsion module is free of rank r
-- statement:
--   Let $A$ be a commutative ring which is a domain and a principal ideal ring, and let $D$ be an $A$-module (an additive commutative group with an $A$-module structure) which is a torsion module in the sense of `Module.IsTorsion A D`: every element of $D$ is annihilated by some element of the monoid of non-zero-divisors of $A$. Let $r$ be a natural number and let $\pi \colon (\mathrm{Fin}\ r \to A) \to D$ be an $A$-linear map from the free module of rank $r$ on the index type $\mathrm{Fin}\ r$. The assertion is that there exists an $A$-linear endomorphism $\varphi$ of $\mathrm{Fin}\ r \to A$ which is injective as a function and whose range, as a submodule, is exactly the kernel of $\pi$. Thus $\ker \pi$ is the image of an injective self-map of $A^r$, hence free of rank exactly $r$; no surjectivity of $\pi$ is assumed, so the conclusion is the exactness statement $0 \to A^r \xrightarrow{\varphi} A^r \xrightarrow{\pi} D$ together with $\operatorname{im}\varphi = \ker\pi$ rather than a full free resolution.
--
--   This is the stacked-bases (Smith normal form) theorem for submodules of a finitely generated free module over a principal ideal domain, in the sharp form that the quotient being torsion forces the submodule to have full rank. It supplies the first step of a two-term free resolution $0 \to A^r \to A^r \to D \to 0$ of a torsion module, and is used in the construction of free resolutions for nilpotent Honda systems via [`Deformation.HondaSystem.exists_free_resolution_of_isNilpotent`](thm.html#Deformation.HondaSystem.exists_free_resolution_of_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_injective_range_eq_ker_of_isTorsion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem LinearMap.exists_injective_range_eq_ker_of_isTorsion
    {A : Type u} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {D : Type v} [AddCommGroup D] [Module A D] (hD : Module.IsTorsion A D)
    {r : ℕ} (π : (Fin r → A) →ₗ[A] D) :
    ∃ φ : (Fin r → A) →ₗ[A] (Fin r → A),
      Function.Injective φ ∧ LinearMap.range φ = LinearMap.ker π := by sorry
