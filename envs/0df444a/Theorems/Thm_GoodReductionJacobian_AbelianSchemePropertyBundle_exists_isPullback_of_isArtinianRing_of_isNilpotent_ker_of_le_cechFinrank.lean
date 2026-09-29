-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_of_isArtinianRing_of_isNilpotent_ker_of_le_cechFinrank
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_of_isArtinianRing_of_isNilpotent_ker_of_le_cechFinrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/3b8fac91-1fc0-5b03-ab8e-4bb797f1953f
-- title:
--   Lifting abelian schemes along nilpotent surjections of Artinian bases
-- statement:
--   Let $T'$ be a commutative local Artinian ring whose residue field is algebraically closed, let $T$ be a commutative ring, and let $\pi : T' \to T$ be a surjective ring homomorphism whose kernel is a nilpotent ideal. Let $f_0 : A_0 \to \operatorname{Spec} T$ be a morphism of schemes equipped with a relative group law $L_0$ (a group structure, functorial in the test scheme, on the sets of sections $\{\varphi : S \to A_0 \mid \varphi \circ f_0 = t\}$ for $t : S \to \operatorname{Spec} T$) that is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f_0$: $f_0$ is smooth and proper, each fibre $f_0^{-1}(s)$ of the underlying map of spaces is connected, and $f_0$ admits some relative group law. Assume further that there exist an algebraically closed field $k$, a morphism $f_k : A_k \to \operatorname{Spec} k$, a ring homomorphism $\rho : T \to k$ and a morphism $i : A_k \to A_0$ making $A_k$ the base change of $f_0$ along $\operatorname{Spec} \rho$, a natural number $g$ with $f_k$ smooth of relative dimension $g$, and a finite linearly ordered affine open cover $\mathcal{K}$ of $A_k$ such that $g \le \dim_k$ of the first Čech cohomology of the structure sheaf of $A_k$ computed from $\mathcal{K}$. The conclusion asserts the existence of a scheme $A$, a morphism $f : A \to \operatorname{Spec} T'$, a commutative relative group law $L$ on $f$, the same bundle of properties `AbelianSchemePropertyBundle` for $f$, and a morphism $g : A_0 \to A$ exhibiting $f_0$ as the base change of $f$ along $\operatorname{Spec} \pi$, such that $g$ is a homomorphism for the group laws: for every scheme $S$, every $t : S \to \operatorname{Spec} T$ and all sections $P, Q$ of $f_0$ over $t$, composing $L_0.\mathrm{mul}\,t\,P\,Q$ with $g$ gives $L.\mathrm{mul}$ at $t$ followed by $\operatorname{Spec} \pi$ applied to $P$ followed by $g$ and $Q$ followed by $g$.
--
--   This is the existence half of the deformation theory of abelian schemes — unobstructedness of lifting along a surjection of Artinian local rings with nilpotent kernel, here formulated for smooth proper morphisms with connected fibres carrying a commutative group law on points, with the vanishing input recorded as a bound on the first Čech cohomology of the structure sheaf of the geometric closed fibre. It is obtained from the case of a small kernel by induction, and is used in the construction of lifts with compatible group-scheme actions and of formal coordinates on deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isPullback_of_isArtinianRing_of_isNilpotent_ker_of_le_cechFinrank.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isPullback_of_isArtinianRing_of_isNilpotent_ker_of_le_cechFinrank
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    (hH1 : ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (Ak : Scheme.{u}) (fk : Ak ⟶ Spec (CommRingCat.of k)) (i : Ak ⟶ A₀) (ρ : T →+* k)
      (_ : IsPullback i fk f₀ (Spec.map (CommRingCat.ofHom ρ))) (g : ℕ) (_ : SmoothOfRelativeDimension g fk)
      (𝒦 : Ak.OrderedAffineCover), g ≤ (OModulePresheaf.unit fk).cechFinrank 𝒦 1) :
    ∃ (A : Scheme.{u}) (f : A ⟶ Spec (CommRingCat.of T')) (L : RelativeGroupLaw T' f) (_ : L.IsCommutative)
      (_ : AbelianSchemePropertyBundle T' f)
      (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π))),
      ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) (P Q : SchemeHomOver t f₀),
        (L₀.mul t P Q).1 ≫ g =
          (L.mul (t ≫ Spec.map (CommRingCat.ofHom π))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1 := by sorry
