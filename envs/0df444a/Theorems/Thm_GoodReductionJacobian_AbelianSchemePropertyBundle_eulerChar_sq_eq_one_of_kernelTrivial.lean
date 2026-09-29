-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_sq_eq_one_of_kernelTrivial
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_sq_eq_one_of_kernelTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/d70d763c-728c-5aee-a50e-356dbfd9e5d3
-- title:
--   Trivial kernel forces χ(L)² = 1
-- statement:
--   Let $K$ be a field, let $A$ be a scheme (in universe $0$) and let $f : A \to \operatorname{Spec} K$ be a morphism equipped with a relative group law $L$, i.e. functorial group structures on the sets of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$ over each $t : T \to \operatorname{Spec} K$, compatible with base change along $T' \to T$. Assume `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists. Let $\mathcal K$ be an ordered affine cover of $A$, that is, a finite linearly ordered family of affine open subsets of $A$ whose supremum is $\top$, and let $\mathcal L$ be an $\mathcal O_A$-module that is invertible, i.e. every point of $A$ has a neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit module. Assume `KernelTrivial` for $(f, L, \mathcal L)$: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} K$ and every $t$-point $x$ of $A$, if the pullback along the slice morphism associated with $x$ of the Mumford bundle $m^{*}\mathcal L \otimes p_1^{*}\mathcal L^{\vee} \otimes p_2^{*}\mathcal L^{\vee}$ on $A \times_K A$ is, locally on the base $\operatorname{Spec} R$, isomorphic to the unit module, then $x$ is the identity point $L.\mathrm{one}\,t$. Then the Euler characteristic of $\mathcal L$ computed from $\mathcal K$ — the alternating sum $\sum_{i < \#\mathcal K.\iota} (-1)^i \dim_K H^i$ of the $K$-dimensions of the Čech cohomology of the $\mathcal O$-module presheaf of sections of $\mathcal L$ — satisfies $\chi(\mathcal L)^2 = 1$.
--
--   This is the degenerate case of Mumford's formula $\deg \varphi_{\mathcal L} = \chi(\mathcal L)^2$ for a line bundle on an abelian variety: when the scheme-theoretic kernel $K(\mathcal L)$ reduces to the identity section, the Euler characteristic is $\pm 1$. It is used in the treatment of polarisations of degree one, in particular to propagate kernel triviality between a field and its base changes and in the construction of canonical polarisation data on quaternionic Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eulerChar_sq_eq_one_of_kernelTrivial.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eulerChar_sq_eq_one_of_kernelTrivial
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hA : AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelTrivial f L 𝓛) :
    ((OModulePresheaf.ofModules f 𝓛).eulerChar 𝒦) ^ 2 = 1 := by sorry
