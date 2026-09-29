-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap
-- name    : NumberField.TateGlobal.exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/c677d6f2-2c84-53a5-a342-252247bfecd2
-- title:
--   Borel fundamental domain for the principal ideles
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$, and let the unit group $\mathbb{A}_F^\times$ (the units of the topological ring $\mathbb{A}_F$, carrying its usual topological group structure) be equipped with a measurable space structure which is assumed to be the Borel $\sigma$-algebra of that topology. Write $\Gamma$ for the subgroup of $\mathbb{A}_F^\times$ obtained by applying `Units.map` to the monoid homomorphism underlying the structure map $\mathrm{algebraMap}\colon F \to \mathbb{A}_F$, that is, the range of the induced map $F^\times \to \mathbb{A}_F^\times$: the group of principal ideles. The assertion is the existence of a single subset $\Omega \subseteq \mathbb{A}_F^\times$ which is measurable and which, simultaneously for every measure $\nu$ on $\mathbb{A}_F^\times$, is a fundamental domain for the multiplicative action of $\Gamma$ on $\mathbb{A}_F^\times$ in the sense of `MeasureTheory.IsFundamentalDomain`: $\Omega$ is null-measurable, the translates $\gamma \cdot \Omega$ for $\gamma \in \Gamma$ cover $\mathbb{A}_F^\times$ up to a $\nu$-null set, and distinct translates meet in $\nu$-null sets. No hypothesis of Haar-ness, local finiteness or $\sigma$-finiteness is placed on $\nu$, and $\Omega$ does not depend on $\nu$.
--
--   This is the measure-theoretic input that makes the quotient $\mathbb{A}_F^\times / F^\times$ usable as a domain of integration: the principal ideles sit discretely in the idele group, so a Borel transversal exists and serves as a fundamental domain for all measures at once. It underlies the unfolding of Tate-type and Godement–Jacquet-type global integrals, and is cited in the computation of the residue-type constants for adelic automorphic integrals, in convergence estimates for Godement sections, and in the Rankin–Selberg analysis of Godement–Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.TateGlobal.exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] :
    ∃ Ω : Set (AdeleRing (𝓞 F) F)ˣ, MeasurableSet Ω ∧
      ∀ ν : Measure (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν := by sorry
