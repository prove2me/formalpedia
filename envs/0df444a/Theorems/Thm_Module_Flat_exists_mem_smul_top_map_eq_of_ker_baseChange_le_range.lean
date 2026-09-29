-- Prove2me | Theorems.Thm_Module_Flat_exists_mem_smul_top_map_eq_of_ker_baseChange_le_range
-- name    : Module.Flat.exists_mem_smul_top_map_eq_of_ker_baseChange_le_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/489258c6-0583-55c5-9363-d66e5f111834
-- title:
--   Cocycles in I C₁ come from I C₀
-- statement:
--   Let $R$ be a commutative ring and $k$ a field equipped with an $R$-algebra structure such that the structure map $\operatorname{algebraMap} R\,k$ is surjective; write $\mathfrak m$ for its kernel. Let $I$ be an ideal of $R$ with $I\cdot\mathfrak m=0$. Let $C_0,C_1,C_2$ be $R$-modules with $C_1$ and $C_2$ flat over $R$, and let $d_0\colon C_0\to C_1$ and $d_1\colon C_1\to C_2$ be $R$-linear maps (no hypothesis $d_1\circ d_0=0$ is imposed). Assume exactness at the middle term after base change to $k$, in the weak form $\ker(d_1\otimes_R k)\subseteq\operatorname{im}(d_0\otimes_R k)$ as submodules of $k\otimes_R C_1$. Then for every $c$ lying in the submodule $I\cdot C_1$, that is in $I\bullet\top$, with $d_1 c=0$, there exists $b$ in the submodule $I\cdot C_0$ with $d_0 b=c$. Equivalently, $I\,C_1\cap\ker d_1\subseteq d_0(I\,C_0)$. All three modules and the rings live in a single universe $u$.
--
--   This is the small-extension step underlying cohomology and base change: over a ring with an ideal $I$ annihilated by the kernel of $R\to k$, exactness of a flat complex at the middle term after reduction to $k$ forces $I$-valued cocycles to be boundaries of $I$-valued cochains. It is used in the construction of local sections of pullbacks of module complexes on schemes, via [`AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_pullbackLocalSection_eq_of_ker_mul_maximalIdeal_eq_bot_of_forall_subsingleton_HSucc).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_exists_mem_smul_top_map_eq_of_ker_baseChange_le_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem Module.Flat.exists_mem_smul_top_map_eq_of_ker_baseChange_le_range
    {R : Type u} [CommRing R] (k : Type u) [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (I : Ideal R) (hI : I * RingHom.ker (algebraMap R k) = ⊥)
    {C₀ C₁ C₂ : Type u} [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
    [Module.Flat R C₁] [Module.Flat R C₂]
    (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂)
    (hex : LinearMap.ker (d₁.baseChange k) ≤ LinearMap.range (d₀.baseChange k))
    (c : C₁) (hc : c ∈ I • (⊤ : Submodule R C₁)) (hdc : d₁ c = 0) :
    ∃ b ∈ I • (⊤ : Submodule R C₀), d₀ b = c := by sorry
