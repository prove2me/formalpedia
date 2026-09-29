-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_pos_of_closedImmersionBySections
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.geomFibreH0Finrank_pos_of_closedImmersionBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/bd5e2483-6c10-53a0-819c-9df7e5fc2ba3
-- title:
--   Positive h⁰ on geometric fibres of a Proj-presented line bundle
-- statement:
--   Let $R$ be a commutative ring and let $f : A \to \operatorname{Spec} R$ be a morphism of schemes (in the bottom universe) satisfying `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth, proper, the fibre $f^{-1}(\{s\})$ of the underlying continuous map over each point $s$ of $\operatorname{Spec} R$ is connected, and there is a relative group law on $f$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} R$, associative, unital, with inverses, and natural in $T$). Let $\mathcal L$ be a module over $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit sheaf of $U$, and assume `ClosedImmersionBySections`: for some $N$ there are a family $\sigma_0,\dots,\sigma_N$ of global sections of $\mathcal L$ and a morphism $\mathrm{toProj} : A \to \operatorname{Proj} R[x_0,\dots,x_N]$ over $\operatorname{Spec} R$ such that on each open contained in $\mathrm{toProj}^{-1}D_+(x_i)$ multiplication by $\sigma_i$ is a bijection from functions to sections, the $\sigma_j$ are obtained from $\sigma_i$ by scaling with the pulled-back ratio $x_j/x_i$, and $\mathrm{toProj}$ is a closed immersion. Finally let $k$ be an algebraically closed field and $sk : R \to k$ a ring homomorphism. Then $0 <$ `geomFibreH0Finrank f 𝓛 k sk`, the $k$-dimension of the global sections of the pullback of $\mathcal L$ to $A \times_{\operatorname{Spec} R} \operatorname{Spec} k$ along the first projection, viewed as a $k$-module through the second projection.
--
--   This is the non-vanishing (together with finiteness, implicit in the use of `Module.finrank`) of $h^0$ of the restriction of a relatively very ample invertible module to a geometric fibre of an abelian scheme. It feeds the study of polarisations, being cited in the proof that the relevant successor space is subsingleton over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_pos_of_closedImmersionBySections.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.geomFibreH0Finrank_pos_of_closedImmersionBySections
    {R : Type} [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f)
    (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k) :
    0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk := by sorry
