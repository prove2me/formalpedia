-- Prove2me | Theorems.Thm_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
-- name    : Module.Flat.projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/1d9e2e41-0b39-539e-801c-a08997c2ccbd
-- title:
--   Base change of ker d⁰ where g becomes invertible
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $C_i$ ($i \in \mathbb{N}$) be flat $R$-modules and let $d_i : C_i \to C_{i+1}$ be $R$-linear maps with $d_{i+1} \circ d_i = 0$ for all $i$; assume the complex is bounded in the sense that there is an $n$ with $C_i$ a subsingleton for all $i \ge n$, and that $\ker d_0$ is a finitely generated $R$-module. Let $g \in R$ and let $S$ be an $R$-algebra realising the localisation of $R$ away from $g$, and assume that the base-changed complex over $S$ is exact in positive degrees, i.e. $\ker(d_{i+1} \otimes S) \le \operatorname{im}(d_i \otimes S)$ for every $i$. Then for every commutative $R$-algebra $A$ (in the same universe) in which the image of $g$ under $\operatorname{algebraMap} R A$ is a unit, the following hold: $\ker(d_0 \otimes A)$ is a finitely generated $A$-module; it is a projective $A$-module; $\ker(d_{i+1} \otimes A) \le \operatorname{im}(d_i \otimes A)$ for every $i$; and the comparison map [`TwoChartCech.kerBaseChangeHom (d 0) A`](def/AlgebraicGeometry_TwoChartCech.html#L123), namely the $A$-linear map $A \otimes_R \ker d_0 \to \ker(d_0 \otimes A)$ obtained by base-changing the inclusion $\ker d_0 \hookrightarrow C_0$ and corestricting it to $\ker(d_0 \otimes A)$, is bijective.
--
--   This is a cohomology-and-base-change statement for a bounded complex of flat modules, localised form: exactness in positive degrees after inverting a single element $g$ propagates to every algebra in which $g$ is invertible, and there it forces $\ker d_0$ to be finitely generated projective with formation of $\ker d_0$ commuting with base change. It feeds the statement [`Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range`](thm.html#Module.Flat.exists_forall_isUnit_projective_ker_baseChange_of_ker_baseChange_residueField_le_range), which produces such an element $g$ from exactness over a residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (g : R) (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away g S]
    (hex : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange S) ≤ LinearMap.range ((d i).baseChange S))
    (A : Type u) [CommRing A] [Algebra R A] (hA : IsUnit (algebraMap R A g)) :
    Module.Finite A (LinearMap.ker ((d 0).baseChange A)) ∧
      Module.Projective A (LinearMap.ker ((d 0).baseChange A)) ∧
      (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)) ∧
      Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A) := by sorry
