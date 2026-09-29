-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b5c00c34-02bb-5e56-8470-24dfc7095b28
-- title:
--   Base change of a p-divisible group inside a relative group law
-- statement:
--   Let $R$ be a commutative ring, $f : J \to \operatorname{Spec} R$ a scheme over $R$, and $L$ a relative group law on $f$, i.e. a functorial group structure on the sets of sections $\{\varphi : T \to J \mid \varphi \circ\!\!\!\!\cdot\, f = t\}$ for morphisms $t : T \to \operatorname{Spec} R$, assumed commutative; let $p$ be prime, $h$ a natural number, and $G$ a $p$-divisible group over $R$ of height $h$ (finite free cocommutative Hopf algebras $G.\mathrm{level}\,v$ of rank $p^{vh}$, surjective bialgebra transitions with kernel the $p^v$-torsion ideal). Suppose given morphisms $\iota_v : \operatorname{Spec}(G.\mathrm{level}\,v) \to J$ such that: $\iota_v$ lies over $\operatorname{Spec} R$ via $\operatorname{Spec}$ of the structure map (hS1); each $\iota_v$ is a closed immersion (hS2); for every $R$-algebra $B$ and $x, y \in G.\mathrm{Point}\,B\,v$ (algebra maps $G.\mathrm{level}\,v \to B$ under convolution), whose associated $B$-points of $J$ are sections over $\operatorname{Spec} B$, the point attached to $xy$ is the $L$-product of those of $x$ and $y$ (hS5); $\iota_{v+1}$ composed with $\operatorname{Spec}$ of the transition is $\iota_v$ (hS6); and for each $v$ the composite of $\iota_v$ with the $L$-multiplication-by-$p^v$ map equals the constant unit section, the resulting morphism from $\operatorname{Spec}(G.\mathrm{level}\,v)$ to the pullback of this multiplication along the unit section being an isomorphism (hS8). Let $R'$ be a nontrivial commutative $R$-algebra and $\sigma : \operatorname{Spec} R' \to \operatorname{Spec} R$ the induced morphism. The conclusion asserts the existence of morphisms $\iota'_v : \operatorname{Spec}\big((G.\mathrm{baseChange}\,R').\mathrm{level}\,v\big) = \operatorname{Spec}(R' \otimes_R G.\mathrm{level}\,v) \to J \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ with the following six properties: $\iota'_v$ lies over $\operatorname{Spec} R'$ through the second projection; composing $\iota'_v$ with the first projection gives $\operatorname{Spec}$ of the right inclusion $G.\mathrm{level}\,v \to R' \otimes_R G.\mathrm{level}\,v$ followed by $\iota_v$; each $\iota'_v$ is a closed immersion; for every $R'$-algebra $B$ the points of $(G.\mathrm{baseChange}\,R')$ of level $v$ map multiplicatively into the base-changed law $L.\mathrm{baseChange}\,\sigma$, exactly as in hS5; the $\iota'_v$ are compatible with the transitions $\mathrm{id} \otimes G.\mathrm{transition}\,v$; and the analogue of hS8 holds for $L.\mathrm{baseChange}\,\sigma$, so that $\operatorname{Spec}(R' \otimes_R G.\mathrm{level}\,v)$ is carried isomorphically onto the kernel of multiplication by $p^v$. Finally, for every endomorphism $E$ of $J \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ over $\operatorname{Spec} R'$ which is a homomorphism for $L.\mathrm{baseChange}\,\sigma$ (post-composition with $E$ commutes with the group multiplication on sections over every base $s : T \to \operatorname{Spec} R'$), there is a family $\psi_v$ of $R'$-bialgebra endomorphisms of the levels $R' \otimes_R G.\mathrm{level}\,v$, commuting with the transitions, such that $\operatorname{Spec}(\psi_v)$ followed by $\iota'_v$ equals $\iota'_v$ followed by $E$.
--
--   This is the statement that the $p$-divisible group attached to a relative group law, together with the identification of its levels with the $p^v$-torsion subschemes, commutes with an arbitrary base change $R \to R'$, and that endomorphisms of the base-changed scheme which respect the group law — which need not come from endomorphisms over $R$ — restrict to transition-compatible bialgebra endomorphisms of the base-changed levels. It is used in the construction of the finite part of a Néron object at $p$ for modular curves, in the lemmas producing the Raynaud quotient and its descent and the idempotent decomposition of the component Jacobians over the residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion
    {R : Type} [CommRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (p h : ℕ) [Fact p.Prime] (G : PDivisibleGroup R p h)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (G.level v)) ⟶ J)

    (hS1 : ∀ v : ℕ, ι v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (G.level v))))

    (hS2 : ∀ v : ℕ, IsClosedImmersion (ι v))

    (hS5 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R B] (x y : G.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap R B))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : G.level v →ₐ[R] B) : G.level v →+* B)) ≫ ι v =
        (L.mul (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

    (hS6 : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (G.transition v : G.level (v + 1) →+* G.level v)) ≫ ι (v + 1) = ι v)

    (hS8 : ∀ (v : ℕ), ∃ h3 : ι v ≫ L.schemeNsmul (p ^ v) = (ι v ≫ f) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1,
      IsIso (pullback.lift (f := L.schemeNsmul (p ^ v)) (g := (L.one (𝟙 (Spec (CommRingCat.of R)))).1) (ι v) (ι v ≫ f) h3))

    (R' : Type) [CommRing R'] [Nontrivial R'] [Algebra R R'] :
    let σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R R'))

    ∃ ι' : ∀ v : ℕ, Spec (CommRingCat.of ((G.baseChange R').level v)) ⟶ pullback f σ,

      (∀ v : ℕ, ι' v ≫ pullback.snd f σ = Spec.map (CommRingCat.ofHom (algebraMap R' ((G.baseChange R').level v)))) ∧
      (∀ v : ℕ, ι' v ≫ pullback.fst f σ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : G.level v →+* (G.baseChange R').level v)) ≫ ι v) ∧

      (∀ v : ℕ, IsClosedImmersion (ι' v)) ∧

      (∀ (v : ℕ) (B : Type) [CommRing B] [Algebra R' B] (x y : (G.baseChange R').Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (G.baseChange R').level v →ₐ[R'] B) : (G.baseChange R').level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (G.baseChange R').level v →ₐ[R'] B) : (G.baseChange R').level v →+* B)) ≫ ι' v) ≫ pullback.snd f σ =
          Spec.map (CommRingCat.ofHom (algebraMap R' B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (G.baseChange R').level v →ₐ[R'] B) : (G.baseChange R').level v →+* B)) ≫ ι' v =
          ((L.baseChange σ).mul (Spec.map (CommRingCat.ofHom (algebraMap R' B))) ⟨_, hx⟩ ⟨_, hy⟩).1) ∧

      (∀ v : ℕ, Spec.map (CommRingCat.ofHom
          ((G.baseChange R').transition v : (G.baseChange R').level (v + 1) →+* (G.baseChange R').level v)) ≫ ι' (v + 1) = ι' v) ∧

      (∀ (v : ℕ), ∃ h3 : ι' v ≫ (L.baseChange σ).schemeNsmul (p ^ v) =
            (ι' v ≫ pullback.snd f σ) ≫ ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1,
        IsIso (pullback.lift (f := (L.baseChange σ).schemeNsmul (p ^ v)) (g := ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1)
          (ι' v) (ι' v ≫ pullback.snd f σ) h3)) ∧

      (∀ (E : NeronModelInfra.SchemeHomOver (pullback.snd f σ) (pullback.snd f σ)),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R')) (x y : NeronModelInfra.SchemeHomOver s (pullback.snd f σ)),
          NeronModelInfra.schemeHomOverComp ((L.baseChange σ).mul s x y) E =
            (L.baseChange σ).mul s (NeronModelInfra.schemeHomOverComp x E) (NeronModelInfra.schemeHomOverComp y E)) →
        ∃ ψ : ∀ v : ℕ, (G.baseChange R').level v →ₐc[R'] (G.baseChange R').level v,
          (∀ v : ℕ, ((G.baseChange R').transition v).comp (ψ (v + 1)) = (ψ v).comp ((G.baseChange R').transition v)) ∧
          ∀ v : ℕ, Spec.map (CommRingCat.ofHom (ψ v : (G.baseChange R').level v →+* (G.baseChange R').level v)) ≫ ι' v = ι' v ≫ E.1) := by sorry
