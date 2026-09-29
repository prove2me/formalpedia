-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isSymmetric_kernelTrivial_locIsoOnBase_of_kernelTrivial_of_isAlgClosed
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isSymmetric_kernelTrivial_locIsoOnBase_of_kernelTrivial_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/0a41c755-d0d0-5d87-a6b8-26523099d2c5
-- title:
--   Symmetrising an invertible sheaf with trivial kernel
-- statement:
--   Let $k$ be an algebraically closed field and let $f\colon A\to\operatorname{Spec}k$ be a scheme over $k$ carrying a relative group law $L$, that is, a functorial group structure on the sets $\{\varphi\colon T\to A \mid \varphi\circ f=t\}$ of sections of $f$ over arbitrary $k$-schemes $t\colon T\to\operatorname{Spec}k$, natural in $T$; assume $L$ is commutative, and that $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre of $f$ is connected, and $f$ admits a relative group law. Let $\mathcal L_0$ be a module on $A$ that is invertible, meaning each point of $A$ has a neighbourhood on which $\mathcal L_0$ restricts to the unit sheaf, and assume $\mathcal L_0$ has trivial kernel: for every commutative ring $R$, every $t\colon\operatorname{Spec}R\to\operatorname{Spec}k$ and every section $x$ of $f$ over $t$, if the pullback along $\mathrm{sliceAt}(x)$ of the Mumford bundle $m^*\mathcal L_0\otimes p_1^*\mathcal L_0^{\vee}\otimes p_2^*\mathcal L_0^{\vee}$ on $A\times_k A$ is, locally on $\operatorname{Spec}R$, isomorphic to the unit object, then $x$ is the identity section. Then there exists an invertible module $\mathcal L_0'$ on $A$ which again has trivial kernel in this sense, which is symmetric in the sense that $\nu^*\mathcal L_0'$ and $\mathcal L_0'$ are locally on $\operatorname{Spec}k$ isomorphic, where $\nu=$ `negMor f L` is the inversion morphism obtained from $L.\mathrm{inv}$ applied to the identity section, and such that $\mathcal L_0'\otimes\nu^*\mathcal L_0'$ and $\mathcal L_0\otimes\nu^*\mathcal L_0$ are locally on $\operatorname{Spec}k$ isomorphic.
--
--   This is the standard step replacing a line bundle with trivial kernel (a principal bundle) on an abelian variety over an algebraically closed field by a symmetric one with the same symmetric square, obtained by translating by a $2$-divisor of a suitable class in $\operatorname{Pic}^0$. It feeds the construction of principal square roots over a field and the production of symmetric canonical polarisation data for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isSymmetric_kernelTrivial_locIsoOnBase_of_kernelTrivial_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isSymmetric_kernelTrivial_locIsoOnBase_of_kernelTrivial_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀) :
    ∃ 𝓛₀' : A.Modules, Scheme.Modules.IsInvertible 𝓛₀' ∧ KernelTrivial f L 𝓛₀' ∧ IsSymmetric f L 𝓛₀' ∧
      LocIsoOnBase f (𝓛₀' ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀')
        (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀) := by sorry
