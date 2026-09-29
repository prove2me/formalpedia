-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_law_baseChange_comp_eq_of_comp_eq
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_law_baseChange_comp_eq_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/9d43de32-d12a-5e90-a19e-190356657e35
-- title:
--   Base change of a relative group law along S→ S'→ S''
-- statement:
--   Let $S \to S' \to S''$ be commutative rings with algebra structures forming a scalar tower, let $A$ be a scheme and $f : A \to \operatorname{Spec} S$ a morphism. Here a `RelativeGroupLaw` over a base ring $R$ for a morphism $g$ to $\operatorname{Spec} R$ is the data, for every scheme $T$ and every $t : T \to \operatorname{Spec} R$, of a multiplication, a unit and an inversion on the set `SchemeHomOver t g` of morphisms $T \to$ (source of $g$) whose composite with $g$ is $t$, subject to associativity, the two unit laws, left inverses, and naturality in $T$ along morphisms $\psi$ with $\psi \circ t = t'$. Assume given such a law $L$ for $f$ over $S$, and a law $L'$ over $S'$ for the second projection $A_{S'} := A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to \operatorname{Spec} S'$, compatible with $L$ in the sense that for every $T$, every $t' : T \to \operatorname{Spec} S'$ and all $T$-points $P, Q$ of $A_{S'}$ over $t'$, the first projection $A_{S'} \to A$ applied to $L'$-product of $P$ and $Q$ is the $L$-product, over $t'$ followed by $\operatorname{Spec}$ of $S \to S'$, of the images of $P$ and $Q$ under that projection. The conclusion is that there exists a relative group law $L''$ over $S''$ for $A_{S''} := A \times_{\operatorname{Spec} S} \operatorname{Spec} S'' \to \operatorname{Spec} S''$ whose multiplication satisfies two compatibilities: composing an $L''$-product with the canonical morphism $\kappa : A_{S''} \to A_{S'}$ (the pullback lift of the projection $A_{S''} \to A$ and of $A_{S''} \to \operatorname{Spec} S''$ followed by $\operatorname{Spec}$ of $S' \to S''$) gives the $L'$-product of the $\kappa$-images, and composing it with the projection $A_{S''} \to A$ gives the $L$-product of the images. Only the multiplications are asserted to be compatible; no condition is imposed on the units or inversions of $L''$.
--
--   This is the base-change statement for group laws on $T$-points: a law on the $S'$-base change of $A$ compatible with the law downstairs propagates to the $S''$-base change, compatibly with both. It is used in the construction of fake elliptic curves over Čerednik–Drinfeld data, where a group law obtained over one base ring must be transported along a further ring map (for instance to a localisation) while keeping track of the comparison morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_law_baseChange_comp_eq_of_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_law_baseChange_comp_eq_of_comp_eq
    {S S' S'' : Type} [CommRing S] [CommRing S'] [CommRing S''] [Algebra S S'] [Algebra S S''] [Algebra S' S'']
    [IsScalarTower S S' S'']
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))))
    (hL' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S'))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) :
    ∃ L'' : RelativeGroupLaw S'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'')))),
      (∀ (T : Scheme.{0}) (t'' : T ⟶ Spec (CommRingCat.of S''))
          (P Q : SchemeHomOver t'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))),
          (L''.mul t'' P Q).1 ≫
              pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) ≫
                  Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
                (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                  ← IsScalarTower.algebraMap_eq]) =
            (L'.mul (t'' ≫ Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
              ⟨P.1 ≫ pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))
                  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) ≫
                    Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
                  (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    ← IsScalarTower.algebraMap_eq]),
                by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))
                  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) ≫
                    Spec.map (CommRingCat.ofHom (algebraMap S' S'')))
                  (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                    ← IsScalarTower.algebraMap_eq]),
                by rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ (T : Scheme.{0}) (t'' : T ⟶ Spec (CommRingCat.of S''))
          (P Q : SchemeHomOver t'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S''))))),
          (L''.mul t'' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))) =
            (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'')))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S''))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) := by sorry
