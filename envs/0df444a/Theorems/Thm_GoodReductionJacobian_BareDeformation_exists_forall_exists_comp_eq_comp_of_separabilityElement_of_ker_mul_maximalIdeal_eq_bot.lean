-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot
-- name    : GoodReductionJacobian.BareDeformation.exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/424caf8c-f018-5fba-8e27-d015539976b3
-- title:
--   Correcting a bare deformation so that each Λ-endomorphism lifts
-- statement:
--   Let $S$ be an Artinian local ring whose residue field is algebraically closed of characteristic $\ell$ for a prime $\ell$, and let $S_0$ be an $S$-algebra such that the structure map $S \to S_0$ is surjective, its kernel $I$ is nilpotent, and $I \cdot \mathfrak m_S = 0$. Let $\Lambda$ be a ring and let $e \in (S \otimes_{\mathbb Z} \Lambda) \otimes_S (S \otimes_{\mathbb Z} \Lambda)$ satisfy $\mathrm{mul}'(e) = 1$ and $(x \cdot {-}) \otimes \mathrm{id}$ applied to $e$ equals $\mathrm{id} \otimes ({-} \cdot x)$ applied to $e$ for every $x \in S \otimes_{\mathbb Z} \Lambda$ (a separability element). Let $f_0 : A_0 \to \operatorname{Spec} S_0$ be a morphism of schemes equipped with a relative group law $L_0$ on its $T$-points which is commutative, and with $f_0$ smooth, proper, with connected fibres and admitting a relative group law. Let $\mathrm{act}_0 : \Lambda \to \operatorname{End}(A_0)$ assign to each $x$ an endomorphism over $\operatorname{Spec} S_0$ which is a homomorphism for $L_0$ on all $T$-points, with $\mathrm{act}_0(1) = \mathrm{id}$, $\mathrm{act}_0(xy) = \mathrm{act}_0(y)$ followed by $\mathrm{act}_0(x)$, and $P$ followed by $\mathrm{act}_0(x+y)$ equal to the $L_0$-product of $P \circ \mathrm{act}_0(x)$ and $P \circ \mathrm{act}_0(y)$ for every $T$-point $P$. Assume given one bare deformation $D_0$ of $(f_0, L_0)$ over $S$, that is, a scheme with a commutative relative group law over $S$, smooth and proper with connected fibres, whose base change along $S \to S_0$ is $(f_0, L_0)$ via a morphism $g$ compatible with the group laws on points. Then there exists a bare deformation $D$ of $(f_0, L_0)$ over $S$ such that for every $x \in \Lambda$ there is an endomorphism $\varphi$ of $D.A$ over $\operatorname{Spec} S$ with $\mathrm{act}_0(x)$ followed by $D.g$ equal to $D.g$ followed by $\varphi$.
--
--   This is the obstruction-theoretic step of equivariant infinitesimal lifting across a small surjection of Artinian local rings: the given deformation $D_0$ is replaced by another one over the same base for which every individual endomorphism in the $\Lambda$-action on the special fibre lifts, no compatibility between the lifts $\varphi$ for different $x$ being asserted. It feeds the construction of a deformation carrying a full lifted $\Lambda$-action, used for good reduction of the relevant Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

theorem GoodReductionJacobian.BareDeformation.exists_forall_exists_comp_eq_comp_of_separabilityElement_of_ker_mul_maximalIdeal_eq_bot
    (S S₀ : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [IsAlgClosed (ResidueField S)]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField S) ℓ]
    [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    (hsmall : RingHom.ker (algebraMap S S₀) * maximalIdeal S = ⊥)
    {Λ : Type} [Ring Λ]
    (e : (S ⊗[ℤ] Λ) ⊗[S] (S ⊗[ℤ] Λ)) (he₁ : LinearMap.mul' S (S ⊗[ℤ] Λ) e = 1)
    (he₂ : ∀ x : S ⊗[ℤ] Λ, TensorProduct.map (LinearMap.mulLeft S x) LinearMap.id e =
      TensorProduct.map LinearMap.id (LinearMap.mulRight S x) e)
    {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)} (L₀ : RelativeGroupLaw S₀ f₀)
    (hL₀ : L₀.IsCommutative) (h₀ : AbelianSchemePropertyBundle S₀ f₀)
    (act₀ : Λ → (A₀ ⟶ A₀)) (act₀_over : ∀ x : Λ, act₀ x ≫ f₀ = f₀)
    (act₀_hom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ act₀ x =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨Q.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, Q.2]⟩).1)
    (act₀_one : act₀ 1 = 𝟙 A₀)
    (act₀_mul : ∀ x y : Λ, act₀ (x * y) = act₀ y ≫ act₀ x)
    (act₀_add : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t f₀),
      P.1 ≫ act₀ (x + y) =
        (L₀.mul t ⟨P.1 ≫ act₀ x, by rw [Category.assoc, act₀_over, P.2]⟩
          ⟨P.1 ≫ act₀ y, by rw [Category.assoc, act₀_over, P.2]⟩).1)
    (D₀ : BareDeformation f₀ L₀ S) :
    ∃ D : BareDeformation f₀ L₀ S,
      ∀ x : Λ, ∃ φ : D.A ⟶ D.A, φ ≫ D.f = D.f ∧ act₀ x ≫ D.g = D.g ≫ φ := by sorry
