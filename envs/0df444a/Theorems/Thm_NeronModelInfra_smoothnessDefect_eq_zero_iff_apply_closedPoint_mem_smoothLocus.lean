-- Prove2me | Theorems.Thm_NeronModelInfra_smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus
-- name    : NeronModelInfra.smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/b4db68cf-fc2c-5907-a5d6-23b9db90d795
-- title:
--   Vanishing of Néron's smoothness defect at a discrete-valuation-ring point
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain which is a discrete valuation ring), let $X$ be a scheme and let $f\colon X \to \operatorname{Spec} R$ be a morphism which is locally of finite type. Let $R'$ be a second discrete valuation ring and let $a\colon \operatorname{Spec} R' \to X$ be a morphism of schemes, and assume that the image under $a$ of the zero prime ideal of $R'$, i.e. of the generic point of $\operatorname{Spec} R'$, lies in the smooth locus of $f$. Write $x = a(\mathfrak m_{R'})$ for the image of the closed point, and consider the stalk $\mathcal O_{X,x}$ as an $R$-algebra via the map induced by $f$ and $R'$ as an $\mathcal O_{X,x}$-algebra via the map on stalks induced by $a$ at the closed point. The quantity $\delta(a) = \mathrm{smoothnessDefect}\ f\ a$ is the $R'$-module length (an element of $\mathbb N \cup \{\infty\}$) of the torsion submodule of $R' \otimes_{\mathcal O_{X,x}} \Omega_{\mathcal O_{X,x}/R}$. The assertion is that $\delta(a) = 0$ if and only if $x$ lies in the smooth locus of $f$.
--
--   This is Néron's measure for the defect of smoothness at a discrete-valuation-ring-valued point, and the statement is the criterion that it vanishes exactly when the point specialises into the smooth locus; it is the stopping criterion of Néron's smoothening process. It is used in the construction of smoothenings, namely by [`NeronModelInfra.exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd`](thm.html#NeronModelInfra.exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd) and [`NeronModelInfra.exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension`](thm.html#NeronModelInfra.exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus.lean

import Mathlib
import Definitions.Def_NeronModelInfra_SmoothnessDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.smoothnessDefect_eq_zero_iff_apply_closedPoint_mem_smoothLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    (a : Spec (CommRingCat.of R') ⟶ X)
    (hgen : a (⊥ : PrimeSpectrum R') ∈ f.smoothLocus) :
    smoothnessDefect f a = 0 ↔ a (IsLocalRing.closedPoint R') ∈ f.smoothLocus := by sorry
