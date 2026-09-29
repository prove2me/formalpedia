-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.genericFibreRestrict_surjective_of_quasiCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/e0de8da4-8a78-52aa-957c-0fa12dc7b13c
-- title:
--   Extension of generic-fibre morphisms into an abelian scheme over a DVR
-- statement:
--   Let $R$ be a discrete valuation ring (a domain) and $K$ a field that is a fraction field of $R$ via a fixed $R$-algebra structure, and write $\iota \colon \operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism induced by the structure map $R \to K$. Let $A$ and $T$ be schemes, let $f \colon A \to \operatorname{Spec} R$ satisfy the predicate `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ of the underlying map of topological spaces is connected (and non-empty), and there exists a relative group law on $f$ — a group structure on the sets $\{\varphi \colon Y \to A \mid \varphi \circ g = g'\}$ of $\operatorname{Spec} R$-morphisms into $A$, for all test objects, compatible with composition in the test object. Let $t \colon T \to \operatorname{Spec} R$ be smooth and quasi-compact. Then the generic-fibre base-change map is surjective: for every morphism $u_K$ from $T \times_{\operatorname{Spec} R} \operatorname{Spec} K$ to $A \times_{\operatorname{Spec} R} \operatorname{Spec} K$ commuting with the second projections to $\operatorname{Spec} K$, there is a morphism $\varphi \colon T \to A$ with $\varphi$ followed by $f$ equal to $t$ whose base change along $\iota$, namely the morphism of pullbacks determined by the first projection followed by $\varphi$ and by the second projection, equals $u_K$.
--
--   This is the existence half of the Néron mapping property for abelian schemes over a discrete valuation ring, restricted to quasi-compact smooth test schemes. It is used in the construction of the Néron model property bundle from the abelian scheme property bundle, [`NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle`](thm.html#NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.genericFibreRestrict_surjective_of_quasiCompact
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t] :
    Function.Surjective (genericFibreRestrict R K f t) := by sorry
