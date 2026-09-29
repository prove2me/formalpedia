-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isSymmetric_nonempty_tensor_pullback_negMor_iso_of_kernelPts_finite
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isSymmetric_nonempty_tensor_pullback_negMor_iso_of_kernelPts_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/fffa8020-9991-5c13-b103-69a660018528
-- title:
--   Symmetric invertible sheaf with prescribed L⊗[-1]^*L
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} k$, with associativity, unit, inverse and naturality under base change. Assume $L$ is commutative, and that $f$ satisfies the property bundle `AbelianSchemePropertyBundle`: $f$ is smooth and proper, each fibre of the underlying map of spaces is connected, and $f$ admits a relative group law. Let $\mathcal L_1$ be an $\mathcal O_A$-module that is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L_1$ is isomorphic to the unit module of $U$, and assume the set `kernelPts` $f$ $L$ $\mathcal L_1$ of those $k$-points $x$ of $A$ (sections over the identity of $\operatorname{Spec} k$) lying in the stabiliser of $\mathcal L_1$, i.e. for which the pullback of $\mathcal L_1$ along translation by $x$ is locally isomorphic over the base to the pullback of $\mathcal L_1$ along the first projection, is finite. Then there exists an invertible $\mathcal O_A$-module $\mathcal L_0$ which is symmetric in the sense of `IsSymmetric`, i.e. every point $s$ of $\operatorname{Spec} k$ has an open neighbourhood $U$ such that $(\text{neg})^*\mathcal L_0$ and $\mathcal L_0$ become isomorphic after restriction to $f^{-1}(U)$, where $\text{neg} =$ `negMor` $f$ $L$ is the inversion morphism of $L$, and such that $\mathcal L_0 \otimes \text{neg}^*\mathcal L_0$ is isomorphic to $\mathcal L_1 \otimes \text{neg}^*\mathcal L_1$ (the isomorphism asserted as nonemptiness of the type of isomorphisms).
--
--   This is the standard symmetrisation step for a line bundle on an abelian variety over an algebraically closed field: after translating by a suitable point one may assume the bundle is symmetric without changing $\mathcal L \otimes [-1]^*\mathcal L$. It is used in the construction of canonical polarisation data for quaternionic Shimura curves, being cited by [`CerednikDrinfeld.QM.IsCanonicalPolData.exists_relativeGroupLaw_geomFibre_exists_kernelTrivial_isSymmetric_iso_tensor_self_finrank_pos`](thm.html#CerednikDrinfeld.QM.IsCanonicalPolData.exists_relativeGroupLaw_geomFibre_exists_kernelTrivial_isSymmetric_iso_tensor_self_finrank_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isSymmetric_nonempty_tensor_pullback_negMor_iso_of_kernelPts_finite.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isSymmetric_nonempty_tensor_pullback_negMor_iso_of_kernelPts_finite
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₁ : A.Modules) (h𝓛₁ : Scheme.Modules.IsInvertible 𝓛₁) (hK : (kernelPts f L 𝓛₁).Finite) :
    ∃ 𝓛₀ : A.Modules, Scheme.Modules.IsInvertible 𝓛₀ ∧ IsSymmetric f L 𝓛₀ ∧
      Nonempty (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀ ≅
        𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₁) := by sorry
