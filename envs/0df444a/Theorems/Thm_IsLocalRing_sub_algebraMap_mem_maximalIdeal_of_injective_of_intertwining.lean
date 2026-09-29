-- Prove2me | Theorems.Thm_IsLocalRing_sub_algebraMap_mem_maximalIdeal_of_injective_of_intertwining
-- name    : IsLocalRing.sub_algebraMap_mem_maximalIdeal_of_injective_of_intertwining
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/694ee1eb-1ca5-523a-a278-868adc5bafe7
-- title:
--   Residual values transfer along an injective intertwining map
-- statement:
--   Let $\mathcal{O}$ be a commutative noetherian local ring, let $R_0$ be a commutative local $\mathcal{O}$-algebra which is finite as an $\mathcal{O}$-module, and let $R_a$ be a commutative local $\mathcal{O}$-algebra. Let $C_0$ be an abelian group carrying compatible $\mathcal{O}$-module and $R_0$-module structures (a scalar tower $\mathcal{O} \to R_0 \to C_0$), and let $C_a$ be an abelian group carrying compatible $\mathcal{O}$-module and $R_a$-module structures, with $C_a$ finite as an $\mathcal{O}$-module. Let $F \colon C_0 \to C_a$ be an injective $\mathcal{O}$-linear map, and suppose $C_0$ contains an element $m_0 \neq 0$. Let $x \in R_0$, $y \in R_a$ and $u \in \mathcal{O}$ be such that $x - \mathrm{algebraMap}_{\mathcal{O}, R_0}(u)$ lies in the maximal ideal of $R_0$, and such that $F$ intertwines the action of $x$ on $C_0$ with that of $y$ on $C_a$, i.e. $F(x \cdot m) = y \cdot F(m)$ for every $m \in C_0$. Then $y - \mathrm{algebraMap}_{\mathcal{O}, R_a}(u)$ lies in the maximal ideal of $R_a$; that is, the residual value $u$ of $x$ is also the residual value of $y$.
--
--   This is the commutative-algebra mechanism by which a residual eigenvalue of an operator is carried from one local Hecke algebra to another along an injective, equivariant map of cohomology modules: finiteness of $R_0$ over $\mathcal{O}$ makes $x - u$ topologically nilpotent on $C_0$, while the Krull intersection theorem applies to the finite $\mathcal{O}$-module $C_a$. It is used in the construction of refinements of corner data for degeneracy maps between spaces of cusp forms, where the residual eigenvalue of a $U_q$-operator on a local component at one level must be matched with its residual eigenvalue at another.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_sub_algebraMap_mem_maximalIdeal_of_injective_of_intertwining.lean

import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Algebra.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.sub_algebraMap_mem_maximalIdeal_of_injective_of_intertwining
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    {R₀ Rₐ : Type} [CommRing R₀] [IsLocalRing R₀] [Algebra 𝒪 R₀] [Module.Finite 𝒪 R₀]
    [CommRing Rₐ] [IsLocalRing Rₐ] [Algebra 𝒪 Rₐ]
    {C₀ Cₐ : Type} [AddCommGroup C₀] [Module 𝒪 C₀] [Module R₀ C₀] [IsScalarTower 𝒪 R₀ C₀]
    [AddCommGroup Cₐ] [Module 𝒪 Cₐ] [Module Rₐ Cₐ] [IsScalarTower 𝒪 Rₐ Cₐ] [Module.Finite 𝒪 Cₐ]
    (F : C₀ →ₗ[𝒪] Cₐ) (hF : Function.Injective F) (m₀ : C₀) (hm₀ : m₀ ≠ 0)
    (x : R₀) (y : Rₐ) (u : 𝒪) (hx : x - algebraMap 𝒪 R₀ u ∈ IsLocalRing.maximalIdeal R₀)
    (hxy : ∀ m : C₀, F (x • m) = y • F m) :
    y - algebraMap 𝒪 Rₐ u ∈ IsLocalRing.maximalIdeal Rₐ := by sorry
