-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_isNoetherianRing_of_isClopen
-- name    : GoodReductionJacobian.exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_isNoetherianRing_of_isClopen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/68164b5d-2af6-55ff-9df1-7781049af0fc
-- title:
--   Relative group law over the completed local ring at a point of W
-- statement:
--   Let $R$ be a noetherian commutative ring, $f : A \to \operatorname{Spec} R$ a smooth and proper morphism of schemes, and suppose given $N$ and a closed immersion $\iota : A \to \operatorname{Proj}$ of the homogeneous coordinate algebra $R[x_0,\dots,x_N]$ with $\iota$ followed by the structure morphism $\operatorname{ProjSpace.\pi}\,R\,N$ equal to $f$, together with $e$ an element of `SchemeHomOver (𝟙 _) f`, that is a morphism $\operatorname{Spec} R \to A$ whose composite with $f$ is the identity. Let $W \subseteq \operatorname{Spec} R$ be clopen such that for every $s \in W$ the fibre $f^{-1}(s)$ of the underlying continuous map is connected, and such that for every algebraically closed field $k$ and every morphism $\sigma : \operatorname{Spec} k \to \operatorname{Spec} R$ with set-theoretic image contained in $W$, the second projection of the pullback of $f$ along $\sigma$ satisfies `AbelianSchemePropertyBundle`, i.e. it is smooth and proper, all its fibres are connected, and it admits a relative group law. Fix $s \in W$, put $O = R_{\mathfrak p_s}$, let $\widehat O$ be the adic completion of $O$ at its maximal ideal, and let $\mathrm{cmp} : R \to O \to \widehat O$ be the composite. The conclusion asserts that the base change $A \times_{\operatorname{Spec} R} \operatorname{Spec} \widehat O \to \operatorname{Spec} \widehat O$ (the second pullback projection along $\operatorname{Spec}(\mathrm{cmp})$) carries a `RelativeGroupLaw` over $\widehat O$ — a group structure, functorial under base change of the test base, on the sets of sections $T \to A \times \operatorname{Spec}\widehat O$ over each $t : T \to \operatorname{Spec}\widehat O$ — whose unit section for the identity base morphism is exactly the base change of $e$, namely the morphism into the pullback determined by $\operatorname{Spec}(\mathrm{cmp})$ followed by $e$ and the identity.
--
--   This is the formal-completion step in the construction of the group law on a smooth proper family whose geometric fibres over a clopen locus $W$ are abelian varieties: the group law, normalised so that the given section $e$ is the unit, is produced over the completed local ring $\widehat{R_{\mathfrak p_s}}$ at a point of $W$. It is used in turn to descend the group law to the localisation $R_{\mathfrak p_s}$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_isNoetherianRing_of_isClopen.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem GoodReductionJacobian.exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_isNoetherianRing_of_isClopen
    {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hs : Smooth f) (hp : IsProper f)
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (W : Set ↥(Spec (CommRingCat.of R))) (hW : IsClopen W)
    (hc : ∀ s : Spec (CommRingCat.of R), s ∈ W → _root_.IsConnected (f.base ⁻¹' {s}))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Set.range s.base ⊆ W → AbelianSchemePropertyBundle k (pullback.snd f s))
    (s : Spec (CommRingCat.of R)) (hsW : s ∈ W) :
    ∃ L : RelativeGroupLaw (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal))
        (pullback.snd f (Spec.map (CommRingCat.ofHom
          ((algebraMap (Localization.AtPrime s.asIdeal)
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal))).comp
            (algebraMap R (Localization.AtPrime s.asIdeal)))))),
      (L.one (𝟙 _)).1 =
        pullback.lift (Spec.map (CommRingCat.ofHom
          ((algebraMap (Localization.AtPrime s.asIdeal)
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal))).comp
            (algebraMap R (Localization.AtPrime s.asIdeal)))) ≫ e.1) (𝟙 _)
          (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) := by sorry
