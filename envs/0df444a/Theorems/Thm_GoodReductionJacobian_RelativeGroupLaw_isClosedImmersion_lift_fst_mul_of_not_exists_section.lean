-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_lift_fst_mul_of_not_exists_section
-- name    : GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_lift_fst_mul_of_not_exists_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/15263f3a-c3a8-5b3b-9dcb-fe95a4d9fa25
-- title:
--   Translated graph of a non-extending K-point is a closed immersion
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the `IsDiscreteValuationRing` instance) and let $K$ be a field which is an $R$-algebra and the fraction field of $R$; write $\iota : \operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism induced by $R \to K$. Let $f : G \to \operatorname{Spec} R$ be a morphism of schemes that is separated, locally of finite type and quasi-compact, and let $L$ be a relative group law on $f$ over $R$: functorial multiplication, unit and inversion operations on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} R$, satisfying associativity, the two unit laws, left inversion, and compatibility with composition $T' \to T$ on the base. Let $d$ be a $K$-point, that is a morphism $\operatorname{Spec} K \to G$ whose composite with $f$ is $\iota$, and assume $d$ does not extend: there is no $s : \operatorname{Spec} R \to G$ with $s$ followed by $f$ the identity and $\iota$ followed by $s$ equal to $d$. Put $P = G \times_{\operatorname{Spec} R} \operatorname{Spec} K$ with projections $p_1 : P \to G$, $p_2 : P \to \operatorname{Spec} K$, and give $P$ the structure morphism $p_2$ followed by $\iota$. Then the morphism $P \to G \times_{\operatorname{Spec} R} G$ whose two components are $p_1$ and the $L$-product of $p_1$ with the $P$-point $p_2$ followed by $d$ is a closed immersion.
--
--   This is the statement that, for a scheme with a relative group law over a discrete valuation ring, translation by a $K$-point which admits no extension to an $R$-section turns the generic fibre into a closed subscheme of $G \times_R G$ via its translated graph $u \mapsto (u, u\cdot d)$. It is used in the construction of the glued Néron object for $J_0(N)$ at a prime $p$, where such translated graphs provide the closed subschemes along which the gluing is performed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isClosedImmersion_lift_fst_mul_of_not_exists_section.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isClosedImmersion_lift_fst_mul_of_not_exists_section
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R K))) f)
    (hd : ¬ ∃ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.1 = d.1) :
    IsClosedImmersion
      (pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
        (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K)))
          ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl d)).1
        (pullback.condition.trans
          (L.mul (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap R K)))
            ⟨pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))), pullback.condition⟩
            (GoodReductionJacobian.schemeHomOverComp
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) rfl d)).2.symm) :
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ pullback f f) := by sorry
