-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_existsUnique_extension_hom_of_genericFibre
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.existsUnique_extension_hom_of_genericFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/e4a1ee4d-db91-5501-bf82-bee1b80a4355
-- title:
--   Unique extension of a generic-fibre homomorphism to an abelian scheme
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete-valuation-ring property) and let $K$ be a field which is a fraction field of $R$ via a given $R$-algebra structure. Let $A$ and $T$ be schemes, $f : A \to \operatorname{Spec} R$ a morphism satisfying `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth, proper, has connected fibres over every point of $\operatorname{Spec} R$, and admits at least one relative group law; fix in addition a relative group law $L_A$ for $f$, that is, a group structure on the set of $S$-points $\{\varphi : S \to A \mid \varphi \circ f = s\}$ for every $R$-scheme $(S,s)$, with multiplication, unit and inverse satisfying associativity, the unit and inverse laws, and compatibility with pullback along morphisms of $R$-schemes. Let $t : T \to \operatorname{Spec} R$ be smooth, equipped with a relative group law $L_T$. Write $A_K$, $T_K$ for the base changes along $\operatorname{Spec}$ of $R \to K$, with their base-changed group laws. Let $\varphi_K : T_K \to A_K$ be a morphism over $\operatorname{Spec} K$ which is a homomorphism on points: for every $K$-scheme $(S,s)$ and all $S$-points $x,y$ of $T_K$, post-composition with $\varphi_K$ carries the $L_T$-product of $x$ and $y$ to the $L_A$-product of the images. Then there is a unique morphism $\varphi : T \to A$ over $\operatorname{Spec} R$ whose base change to $K$ (formed as the pullback lift) equals $\varphi_K$ and which is likewise a homomorphism on $S$-points for every $R$-scheme $(S,s)$.
--
--   This is the Néron mapping property for abelian schemes over a discrete valuation ring, together with the fact that the resulting extension of a generic-fibre homomorphism is again a homomorphism. It is used in the quaternionic setting to extend morphisms and group actions on fake elliptic curves from the generic fibre to the whole abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_existsUnique_extension_hom_of_genericFibre.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.existsUnique_extension_hom_of_genericFibre
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (LA : RelativeGroupLaw R f)
    {t : T ⟶ Spec (CommRingCat.of R)} [Smooth t] (LT : RelativeGroupLaw R t)
    (φK : SchemeHomOver (RelativeGroupLaw.genericFibreStr K t) (RelativeGroupLaw.genericFibreStr K f))
    (hφK : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K t)),
        NeronModelInfra.schemeHomOverComp ((LT.genericFibre K).mul s x y) φK =
          (LA.genericFibre K).mul s (NeronModelInfra.schemeHomOverComp x φK)
            (NeronModelInfra.schemeHomOverComp y φK)) :
    ∃! φ : SchemeHomOver t f,
      genericFibreRestrict R K f t φ = φK ∧
      ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s t),
        NeronModelInfra.schemeHomOverComp (LT.mul s x y) φ =
          LA.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) := by sorry
