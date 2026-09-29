-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinite_unit_and_eulerChar_unit_eq_zero
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinite_unit_and_eulerChar_unit_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/442a73f3-9499-53df-a388-b66c122beda9
-- title:
--   Čech finiteness and vanishing Euler characteristic of 𝒪_A
-- statement:
--   Let $K$ be an algebraically closed field and $f \colon A \to \operatorname{Spec} K$ a morphism of schemes satisfying `AbelianSchemePropertyBundle K f`, that is: $f$ is smooth, $f$ is proper, the fibre $f^{-1}(s)$ is connected for every point $s$ of $\operatorname{Spec} K$, and there exists a relative group law on $f$ over $K$ (a functorial group structure, with natural multiplication, unit and inverse, on the sets of $T$-points of $A$ over $\operatorname{Spec} K$, for all $K$-schemes $T$). Assume moreover that $f$ is smooth of relative dimension $g$ with $0 < g$, and let $\mathcal{K}$ be an ordered affine cover of $A$: a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq A$, each affine, whose supremum is $A$. Consider the $\mathcal{O}$-module presheaf `OModulePresheaf.unit f`, sending an open $U$ to $\Gamma(A,U)$ with its $K$-algebra structure induced by $f$ and with restriction maps those of the structure sheaf. The conclusion is twofold: first, the associated alternating Čech complex on $\mathcal{K}$ has finite $K$-dimensional cohomology, i.e. the degree-zero group $H^0$ and each higher group are finite $K$-modules; second, the Euler characteristic $\sum_{i < \#\iota} (-1)^i \dim_K H^i$ of that complex vanishes.
--
--   This is the statement $\chi(\mathcal{O}_A) = 0$ for an abelian variety of positive dimension over an algebraically closed field, together with the finite-dimensionality of its (Čech) cohomology, in the Čech formulation on an ordered affine cover used throughout the good-reduction part of the development. It is used in the analysis of the Čech complex in degrees up to two for surfaces, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_sub_sum_cup_mem_range_d_one_of_mem_ker_d_two_of_topologicalKrullDim_eq_two`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_sub_sum_cup_mem_range_d_one_of_mem_ker_d_two_of_topologicalKrullDim_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinite_unit_and_eulerChar_unit_eq_zero.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinite_unit_and_eulerChar_unit_eq_zero
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f] (hg : 0 < g)
    (𝒦 : A.OrderedAffineCover) :
    (OModulePresheaf.unit f).CechFinite 𝒦 ∧ (OModulePresheaf.unit f).eulerChar 𝒦 = 0 := by sorry
