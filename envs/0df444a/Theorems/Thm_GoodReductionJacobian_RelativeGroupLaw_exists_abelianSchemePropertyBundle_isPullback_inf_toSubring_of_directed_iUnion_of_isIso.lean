-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/a16afbf7-353c-5092-9de4-bf3893773b58
-- title:
--   Descending an abelian scheme to a finite level of a directed union
-- statement:
--   Let $k \subseteq \Omega$ be fields with $\Omega$ a $k$-algebra, let $V \subseteq \Omega$ be a subring, and let $(F_i)_{i \in \iota}$ be a monotone family of intermediate fields of $\Omega/k$ indexed by a non-empty directed preorder. Let $Z$ be an intermediate field with $F_i \le Z$ for all $i$ and such that every element of $Z$ lies in some $F_i$. Let $\rho \colon V \sqcap Z \to Z$ and $\tau_i \colon V \sqcap F_i \to F_i$ be ring homomorphisms compatible with the inclusions into $\Omega$ (so $\rho$ and each $\tau_i$ are the evident inclusions). Let $f \colon A \to \operatorname{Spec}(V \sqcap Z)$ carry a relative group law $L$ — a functorial group structure on the sections $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$ for $t \colon T \to \operatorname{Spec}(V \sqcap Z)$, natural in $T$ — which is commutative, and assume `AbelianSchemePropertyBundle`: $f$ is smooth and proper, each fibre $f^{-1}(s)$ over a point of the base is connected, and $f$ admits a relative group law. Let $i_0$ be an index and $f_0 \colon P_0 \to \operatorname{Spec} F_{i_0}$ a quasi-compact, quasi-separated morphism, locally of finite presentation, with a relative group law $L_0$. Assume given an isomorphism $e \colon A \times_{V \sqcap Z} \operatorname{Spec} Z \to P_0 \times_{F_{i_0}} \operatorname{Spec} Z$ over $\operatorname{Spec} Z$ (i.e. $e$ followed by the second projection of the target is the second projection of the source) which is a homomorphism for the base-changed laws: for every $t \colon T \to \operatorname{Spec} Z$ and sections $x,y$ of $A \times_{V \sqcap Z} \operatorname{Spec} Z$ over $t$, the product of $x$ and $y$ for $L$ base-changed along $\operatorname{Spec} \rho$, followed by $e$, equals the product of $x$ followed by $e$ and $y$ followed by $e$ for $L_0$ base-changed along $F_{i_0} \to Z$. Then there are an index $i \ge i_0$, a morphism $f_i \colon A_i \to \operatorname{Spec}(V \sqcap F_i)$ with a commutative relative group law $L_i$ satisfying `AbelianSchemePropertyBundle`, and a morphism $g \colon P_0 \times_{F_{i_0}} \operatorname{Spec} F_i \to A_i$ such that the square formed by $g$, the projection $P_0 \times_{F_{i_0}} \operatorname{Spec} F_i \to \operatorname{Spec} F_i$, $f_i$ and $\operatorname{Spec} \tau_i$ is cartesian, and $g$ is a homomorphism in the same sense: for every $t \colon T \to \operatorname{Spec} F_i$ and sections $x,y$ over $t$, the $L_0$-base-changed product followed by $g$ equals the $L_i$-product, over $t$ followed by $\operatorname{Spec} \tau_i$, of $x$ followed by $g$ and $y$ followed by $g$.
--
--   This is the limit (spreading-out) step which carries an abelian scheme given over the intersection of a subring of $\Omega$ with an infinite intermediate field $Z = \bigcup_i F_i$, together with a prescribed finitely presented generic fibre at level $i_0$, back to a single finite level $i$, in the style of the EGA IV descent and finite-presentation theorems. It is used in the proof of potential good reduction for abelian surfaces with quaternionic multiplication, where $Z$ arises as a directed union of finite extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_abelianSchemePropertyBundle_isPullback_inf_toSubring_of_directed_iUnion_of_isIso
    {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] (V : Subring Ω)
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (F : ι → IntermediateField k Ω) (hF : Monotone F)
    (Z : IntermediateField k Ω) (hFZ : ∀ i, F i ≤ Z) (hZ : ∀ x ∈ Z, ∃ i, x ∈ F i)
    (ρ : ↥(V ⊓ Z.toSubring) →+* ↥Z)
    (hρ : ∀ x : ↥(V ⊓ Z.toSubring), ((ρ x : ↥Z) : Ω) = (x : Ω))
    (τ : ∀ i, ↥(V ⊓ (F i).toSubring) →+* ↥(F i))
    (hτ : ∀ (i) (x : ↥(V ⊓ (F i).toSubring)), ((τ i x : ↥(F i)) : Ω) = (x : Ω))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of ↥(V ⊓ Z.toSubring))}
    (L : RelativeGroupLaw ↥(V ⊓ Z.toSubring) f) (hL : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle ↥(V ⊓ Z.toSubring) f)
    (i₀ : ι) {P₀ : Scheme.{u}} {f₀ : P₀ ⟶ Spec (CommRingCat.of ↥(F i₀))}
    [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀]
    (L₀ : RelativeGroupLaw ↥(F i₀) f₀)
    (e : pullback f (Spec.map (CommRingCat.ofHom ρ)) ⟶
      pullback f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom)))
    [IsIso e]
    (he : e ≫ pullback.snd f₀ _ = pullback.snd f _)
    (hemul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of ↥Z))
        (x y : SchemeHomOver t (pullback.snd f (Spec.map (CommRingCat.ofHom ρ)))),
      ((L.baseChange (Spec.map (CommRingCat.ofHom ρ))).mul t x y).1 ≫ e =
        ((L₀.baseChange (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hFZ i₀)).toRingHom))).mul t
          ⟨x.1 ≫ e, by rw [Category.assoc, he, x.2]⟩ ⟨y.1 ≫ e, by rw [Category.assoc, he, y.2]⟩).1) :
    ∃ (i : ι) (hi : i₀ ≤ i) (Aᵢ : Scheme.{u}) (fᵢ : Aᵢ ⟶ Spec (CommRingCat.of ↥(V ⊓ (F i).toSubring)))
      (Lᵢ : RelativeGroupLaw ↥(V ⊓ (F i).toSubring) fᵢ) (_ : Lᵢ.IsCommutative)
      (_ : AbelianSchemePropertyBundle ↥(V ⊓ (F i).toSubring) fᵢ)
      (g : pullback f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom)) ⟶ Aᵢ)
      (hg : IsPullback g
        (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom)))
        fᵢ (Spec.map (CommRingCat.ofHom (τ i)))),
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of ↥(F i)))
        (x y : SchemeHomOver t
          (pullback.snd f₀ (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom)))),
        ((L₀.baseChange (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (hF hi)).toRingHom))).mul
            t x y).1 ≫ g =
          (Lᵢ.mul (t ≫ Spec.map (CommRingCat.ofHom (τ i)))
            ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1 := by sorry
