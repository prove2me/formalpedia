-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_point_specializes_base_closedPoint
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_point_specializes_base_closedPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/eb5c6503-8775-584c-b074-ef7ae8fd915e
-- title:
--   Every point of a proper K-scheme specialises to a K-point
-- statement:
--   Let $K$ be an algebraically closed field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} K$ be a morphism of schemes. Assume the bundle of properties `AbelianSchemePropertyBundle K f`, that is: $f$ is smooth; $f$ is proper; for every point $s$ of $\operatorname{Spec} K$ the fibre $f^{-1}(\{s\})$, as a subspace of the underlying topological space of $A$, is connected; and there exists a relative group law on $f$ over $K$, namely multiplication, unit and inversion operations on the sets $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ for all $K$-schemes $t : T \to \operatorname{Spec} K$, satisfying associativity, the unit laws and the left inverse law, and compatible with base change along morphisms $\psi : T' \to T$ over $\operatorname{Spec} K$. Let $z$ be a point of the underlying topological space of $A$. Then there is an element $x$ of $\{\varphi : \operatorname{Spec} K \to A \mid \varphi \text{ followed by } f = \mathrm{id}\}$, i.e. a section of $f$, such that $z$ specialises to the image of the closed point of $\operatorname{Spec} K$ under the underlying continuous map of $x$; equivalently, that image lies in the closure of $\{z\}$.
--
--   This is the standard statement that on an abelian variety over an algebraically closed field — here a smooth proper scheme with connected fibres carrying a relative group law — every scheme-theoretic point specialises to a $K$-rational point. It is used in the construction of `exists_affineOpens_isUnit_eigenSubdatum`, where non-vanishing of a function at a specialisation of $z$ is transferred back to $z$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_point_specializes_base_closedPoint.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_point_specializes_base_closedPoint
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (z : A) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f, z ⤳ x.1.base (IsLocalRing.closedPoint K) := by sorry
