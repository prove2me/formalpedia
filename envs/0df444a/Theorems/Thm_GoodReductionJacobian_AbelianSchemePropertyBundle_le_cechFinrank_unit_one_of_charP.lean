-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_le_cechFinrank_unit_one_of_charP
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.le_cechFinrank_unit_one_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/dd57a370-ebf1-57df-b3b8-0612a207ede5
-- title:
--   Lower bound g ≤ dim_K check H¹(A,mathcal O_A) in characteristic p
-- statement:
--   Let $K$ be an algebraically closed field which is of characteristic $p$ for a prime $p$, let $A$ be a scheme and $f : A \to \operatorname{Spec} K$ a morphism. Suppose given a relative group law $L$ on $f$, that is, a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ t = f\text{-section data}\}$ of $T$-points of $A$ over each $t : T \to \operatorname{Spec} K$, with unit, inverse and associativity, and with multiplication compatible with base change along morphisms $\psi : T' \to T$ over $\operatorname{Spec} K$; assume $L$ is commutative, i.e. $L.\mathrm{mul}$ is commutative on every such point set. Assume further the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $g$ be a natural number with $f$ smooth of relative dimension $g$, and let $\mathcal K$ be an ordered affine cover of $A$, i.e. a finite linearly ordered family of affine open subsets of $A$ whose supremum is $\top$. Then $g$ is at most the $K$-dimension of the degree-one alternating Čech cohomology of the structure presheaf, namely the finite rank over $K$ of $\ker d^1 / \operatorname{im} d^0$ for the Čech complex of `OModulePresheaf.unit f` (the presheaf $U \mapsto \Gamma(A,U)$ with its $K$-algebra structure coming from $f$) relative to $\mathcal K$, which is the value of `cechFinrank` at $1$.
--
--   This is the lower bound half of the classical computation $\dim_K H^1(A,\mathcal O_A) = g$ for an abelian variety of dimension $g$ over an algebraically closed field of characteristic $p$, obtained from the structure of the $p$-torsion subgroup scheme. Combined with the matching upper bound it yields the exact value, and it feeds the deformation-theoretic lifting of abelian schemes over Artinian thickenings of residue characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_le_cechFinrank_unit_one_of_charP.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.le_cechFinrank_unit_one_of_charP
    (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (𝒦 : A.OrderedAffineCover) :
    g ≤ (OModulePresheaf.unit f).cechFinrank 𝒦 1 := by sorry
