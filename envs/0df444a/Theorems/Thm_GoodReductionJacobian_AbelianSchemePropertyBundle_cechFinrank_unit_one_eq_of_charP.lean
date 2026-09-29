-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_one_eq_of_charP
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_one_eq_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/00dbf014-c4b8-5dfd-9df9-45ca40b71363
-- title:
--   First Čech cohomology of mathcal O_A has dimension g
-- statement:
--   Let $K$ be an algebraically closed field, $p$ a prime with $K$ of characteristic $p$, and let $f : A \to \operatorname{Spec} K$ be a morphism of schemes. Assume given a relative group law $L$ on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} K$, with multiplication, unit and inverse satisfying associativity, the unit and inverse laws, and compatibility of multiplication with base change along $\psi : T' \to T$ over $\operatorname{Spec} K$; assume $L$ commutative, i.e. $L.\mathrm{mul}\,t\,x\,y = L.\mathrm{mul}\,t\,y\,x$ for all $t$ and all points $x,y$. Assume further the property bundle `AbelianSchemePropertyBundle K f`: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists. Let $g$ be a natural number with $f$ smooth of relative dimension $g$, and let $\mathcal K$ be an ordered affine cover of $A$: a finite linearly ordered index set together with affine opens $U_i \subseteq A$ whose supremum is $A$. Then the Čech invariant in degree $1$ of the $\mathcal O$-module presheaf `OModulePresheaf.unit f` (the presheaf $U \mapsto \Gamma(A,U)$ with its restriction maps, regarded as $K$-modules via $f$) on the cover $\mathcal K$ equals $g$; by definition this is $\dim_K\bigl(\ker d^1/\operatorname{im} d^0\bigr)$, the dimension of $\check H^1(\mathcal K, \mathcal O_A)$.
--
--   This is the classical computation $\dim_K H^1(A,\mathcal O_A) = \dim A$ for an abelian variety, here in the Čech formulation attached to a fixed finite ordered affine cover. It feeds the deformation-theoretic arguments for fake elliptic curves over algebraically closed fields of characteristic $p$, where the tangent space to the deformation functor is computed through this dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_cechFinrank_unit_one_eq_of_charP.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.cechFinrank_unit_one_eq_of_charP
    (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (𝒦 : A.OrderedAffineCover) :
    (OModulePresheaf.unit f).cechFinrank 𝒦 1 = g := by sorry
