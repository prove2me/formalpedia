-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_bareDeformation_dualNumber_isPullback_fst_comp_eq_id
-- name    : GoodReductionJacobian.exists_bareDeformation_dualNumber_isPullback_fst_comp_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/ba8b5a71-0907-5968-a846-a4ad3b2d693c
-- title:
--   The constant first-order deformation of an abelian scheme
-- statement:
--   Let $k$ be a field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, let $L$ be a relative group law on $f$ (functorial group structure on the sets of $T$-points over $\operatorname{Spec} k$, compatible with base change along maps $T' \to T$), assume $L$ commutative and assume the bundle `AbelianSchemePropertyBundle` for $f$, i.e. $f$ smooth and proper with connected fibres and admitting some relative group law. Let $\mathcal{K}$ be an ordered affine cover of $A$ (a finite linearly ordered family of affine opens with supremum $\top$), $i_0$ an index, and let the identity section $L.\mathrm{one}(\mathbf{1})$ factor as $e_A$ followed by the inclusion of $\mathcal{K}.U\,i_0$. Regard $k$ as an algebra over the dual numbers $k[\varepsilon]$ via $\varepsilon \mapsto 0$. Then there exist a bare deformation $D_0$ of $(f,L)$ to $k[\varepsilon]$ — a scheme $D_0.A$ with structure map $D_0.f$ to $\operatorname{Spec} k[\varepsilon]$, a commutative relative group law $D_0.L$ satisfying the same smooth–proper–connected bundle, and a morphism $D_0.g : A \to D_0.A$ cartesian over $\operatorname{Spec}(k[\varepsilon] \to k)$ and multiplicative for the two laws — with $D_0.f$ separated, together with an affine morphism $\pi : D_0.A \to A$ making $(\pi, D_0.f, f, \operatorname{Spec}(k \to k[\varepsilon]))$ a pullback square and satisfying $D_0.g \mathbin{;} \pi = \mathrm{id}_A$, such that: (i) $\pi$ is multiplicative on points, i.e. for all $t : T \to \operatorname{Spec} k[\varepsilon]$ and all $P,Q$ over $t$, the product $D_0.L.\mathrm{mul}\,t\,P\,Q$ composed with $\pi$ equals the $L$-product of $P \mathbin{;} \pi$ and $Q \mathbin{;} \pi$ over $t$ followed by $\operatorname{Spec}(k \to k[\varepsilon])$; (ii) every $\varphi : A \to A$ over $f$ admits a lift $\varphi_0 : D_0.A \to D_0.A$ over $D_0.f$ with $\varphi \mathbin{;} D_0.g = D_0.g \mathbin{;} \varphi_0$ and $\varphi_0 \mathbin{;} \pi = \pi \mathbin{;} \varphi$, which is an endomorphism of the group law $D_0.L$ whenever $\varphi$ is one for $L$; (iii) for each $c \in k$ there is $k_0 : D_0.A \to D_0.A$ cartesian over $\operatorname{Spec}$ of the ring map $\varepsilon \mapsto c\varepsilon$, with $D_0.g \mathbin{;} k_0 = D_0.g$, $k_0 \mathbin{;} \pi = \pi$, and fixing the first projection of the fibre over the residue field of $k[\varepsilon]$; (iv) every $\varphi_0 : D_0.A \to D_0.A$ over $D_0.f$ induces $\psi$ on that residue fibre $D_0.A \times_{k[\varepsilon]} \kappa$ commuting with both projections in the sense $\psi \mathbin{;} \mathrm{pr}_2 = \mathrm{pr}_2$ and $\psi \mathbin{;} \mathrm{pr}_1 = \mathrm{pr}_1 \mathbin{;} \varphi_0$, and $\psi$ is an endomorphism of the base-changed law `RelativeGroupLaw.baseChange` whenever $\varphi_0$ is one of $D_0.L$; and (v) the identity section of $D_0.L$ factors through the member with index $i_0$ of the cover $\mathcal{K}.\mathrm{comap}\,\pi$ obtained by taking $\pi$-preimages.
--
--   This provides the trivial (constant) first-order deformation $A \times_k \operatorname{Spec} k[\varepsilon]$ of an abelian scheme over a field, as the distinguished base point of the set of deformations to the dual numbers, equipped with the projection to $A$, the constant lifts of endomorphisms, the scaling self-base-changes $\varepsilon \mapsto c\varepsilon$, and the restriction of endomorphisms to the closed fibre. It is used in the classification of first-order deformations of a fake elliptic curve over an algebraically closed field of characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_bareDeformation_dualNumber_isPullback_fst_comp_eq_id.lean

import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing Scheme.TwoAffineOpenCover CerednikDrinfeld.QM

theorem GoodReductionJacobian.exists_bareDeformation_dualNumber_isPullback_fst_comp_eq_id
    (k : Type) [Field k]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle k f)

    (𝒦 : A.OrderedAffineCover) (i₀ : 𝒦.ι)
    (eA : Spec (CommRingCat.of k) ⟶ ↑(𝒦.U i₀)) (heA : eA ≫ (𝒦.U i₀).ι = (L.one (𝟙 _)).1) :
    letI : Algebra (DualNumber k) k := (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra
    ∃ (D₀ : BareDeformation f L (DualNumber k)) (_ : IsSeparated D₀.f)
      (π : D₀.A ⟶ A) (_ : IsAffineHom π)
      (hπ : CategoryTheory.IsPullback π D₀.f f (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))))
      (_ : D₀.g ≫ π = 𝟙 A),

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t D₀.f),
        (D₀.L.mul t P Q).1 ≫ π =
          (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
            ⟨P.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, Q.2]⟩).1) ∧

      (∀ (φ : A ⟶ A) (hφ : φ ≫ f = f),
        ∃ (φ₀ : D₀.A ⟶ D₀.A) (hφ₀ : φ₀ ≫ D₀.f = D₀.f), φ ≫ D₀.g = D₀.g ≫ φ₀ ∧ φ₀ ≫ π = π ≫ φ ∧
          ((∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
              pushPt φ hφ (L.mul t P Q) = L.mul t (pushPt φ hφ P) (pushPt φ hφ Q)) →
            ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t D₀.f),
              pushPt φ₀ hφ₀ (D₀.L.mul t P Q) = D₀.L.mul t (pushPt φ₀ hφ₀ P) (pushPt φ₀ hφ₀ Q))) ∧

      (∀ c : k, ∃ k₀ : D₀.A ⟶ D₀.A,
        CategoryTheory.IsPullback k₀ D₀.f D₀.f
          (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)) ∧
        D₀.g ≫ k₀ = D₀.g ∧ k₀ ≫ π = π ∧
        pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))) ≫ k₀ =
          pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) ∧

      (∀ (φ₀ : D₀.A ⟶ D₀.A) (hφ₀ : φ₀ ≫ D₀.f = D₀.f),
        ∃ (ψ : pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))) ⟶
            pullback D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))
          (hψ : ψ ≫ (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k)))) = (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))),
          ψ ≫ pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))) =
            pullback.fst D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))) ≫ φ₀ ∧
          ((∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t D₀.f),
              pushPt φ₀ hφ₀ (D₀.L.mul t P Q) = D₀.L.mul t (pushPt φ₀ hφ₀ P) (pushPt φ₀ hφ₀ Q)) →
            ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField (DualNumber k))))
              (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap (DualNumber k) (ResidueField (DualNumber k))))),
              pushPt ψ hψ ((RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap (DualNumber k) (ResidueField (DualNumber k))) D₀.L).mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))) ∧

      (∃ e₀ : Spec (CommRingCat.of (DualNumber k)) ⟶ ↑((𝒦.comap π).U i₀),
        e₀ ≫ ((𝒦.comap π).U i₀).ι = (D₀.L.one (𝟙 _)).1) := by sorry
