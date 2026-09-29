-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/71b1e2dc-f008-5a87-a7ca-5a528dd4aee3
-- title:
--   Nonzero n-torsion K[ε]-point at the origin
-- statement:
--   Let $K$ be a field, $A$ a scheme with a morphism $f : A \to \operatorname{Spec} K$, and $L$ a relative group law on $f$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ \text{(structure map)} \ldots\}$, i.e. for every $t : T \to \operatorname{Spec} K$ a multiplication, unit and inverse on the $T$-points $\{\varphi : T \to A : \varphi$ followed by $f$ equals $t\}$, satisfying associativity, the unit laws, left inversion and compatibility with base change along morphisms $\psi : T' \to T$ over $\operatorname{Spec} K$. Assume $L$ is commutative, and assume the bundle `AbelianSchemePropertyBundle K f`, namely that $f$ is smooth and proper, that each fibre $f^{-1}(s)$ is connected, and that a relative group law on $f$ exists. Let $g \in \mathbb{N}$ be such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, with $g > 0$, and let $n \in \mathbb{N}$ satisfy $(n : K) = 0$. Then there is a morphism $y : \operatorname{Spec} K[\varepsilon] \to A$ over $\operatorname{Spec}$ of $K \to K[\varepsilon]$, where $K[\varepsilon]$ is the ring of dual numbers, such that the $n$-fold iterate $L.\mathrm{nsmul}\,n\,y$ (defined by $0 \mapsto$ the unit and $k+1 \mapsto$ the product of the $k$-th iterate with $y$) equals the unit section, such that composing $\operatorname{Spec}$ of the projection $K[\varepsilon] \to K$, $\varepsilon \mapsto 0$, with $y$ gives the underlying morphism of the unit section over $\mathrm{id}_{\operatorname{Spec} K}$, and such that $y$ is not the unit section.
--
--   This is the standard statement that on an abelian variety of positive dimension over a field of characteristic dividing $n$ the $n$-torsion is not reduced: there is a nonzero tangent vector at the identity, viewed as a $K[\varepsilon]$-point reducing to the origin, on which $[n]$ acts as multiplication by $(n : K) = 0$. It is used in the polarisation theory of abelian schemes, in [`AlgebraicGeometry.PolarisedAbelianScheme.natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.natCast_add_ne_zero_of_principalRoot_of_rootedSymmetricOfType_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators MonoidalCategory

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero
    {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of K)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g) (hg : 0 < g)
    (n : ℕ) (hn : (n : K) = 0) :
    ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))) f,
      L.nsmul _ n y = L.one _ ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ y.1 = (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ∧
      y ≠ L.one _ := by sorry
