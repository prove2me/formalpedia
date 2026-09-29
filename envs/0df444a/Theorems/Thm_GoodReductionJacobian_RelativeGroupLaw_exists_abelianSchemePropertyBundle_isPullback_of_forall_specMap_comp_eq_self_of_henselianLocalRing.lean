-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_of_forall_specMap_comp_eq_self_of_henselianLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_abelianSchemePropertyBundle_isPullback_of_forall_specMap_comp_eq_self_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/f4affc1e-afe6-5b94-a47a-19f03e392f77
-- title:
--   Néron–Ogg–Shafarevich: unramified ℓ-torsion gives good reduction
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain and a henselian local ring, let $K$ be its field of fractions (an $R$-algebra that is a fraction field of $R$) and let $\Omega$ be an algebraic closure of $K$. Let $g_K \colon A_K \to \operatorname{Spec} K$ be a morphism of schemes equipped with a relative group law $L_{A_K}$, i.e. a group structure on the sets $\{\varphi \colon T \to A_K \mid \varphi \circ g_K = t\}$ of $T$-points over each $t \colon T \to \operatorname{Spec} K$, with multiplication, unit and inverse natural in $T$, and assume `AbelianSchemePropertyBundle K gK`: $g_K$ is smooth and proper, each fibre of the underlying map over a point of $\operatorname{Spec} K$ is connected, and a relative group law on $g_K$ exists. Let $\ell$ be a prime which is a unit in $R$, and assume: for every valuation subring $A$ of $\Omega$ containing the image of $R$, every $K$-automorphism $\sigma$ of $\Omega$ in the inertia subgroup of $A$ over $K$ (the image in $\operatorname{Aut}_K(\Omega)$ of the inertia subgroup inside the decomposition subgroup), every $v \in \mathbb{N}$ and every $\Omega$-point $x$ of $A_K$ over $\operatorname{Spec}\Omega \to \operatorname{Spec} K$ with $\ell^v$-fold $L_{A_K}$-product equal to the unit, one has $\operatorname{Spec}(\sigma)$ followed by $x$ equal to $x$. The conclusion: there exist a scheme $\mathcal A$, a morphism $f_{\mathcal A} \colon \mathcal A \to \operatorname{Spec} R$, a relative group law $L_{\mathcal A}$ on $f_{\mathcal A}$ which is commutative, a proof of `AbelianSchemePropertyBundle R f𝒜`, and a morphism $g \colon A_K \to \mathcal A$ such that the square formed by $g$, $g_K$, $f_{\mathcal A}$ and $\operatorname{Spec} K \to \operatorname{Spec} R$ is a pullback, and such that for every scheme $T$, every $t' \colon T \to \operatorname{Spec} K$ and all $T$-points $x,y$ of $A_K$ over $t'$, the composite of the $L_{A_K}$-product of $x$ and $y$ with $g$ equals the $L_{\mathcal A}$-product, over $t'$ followed by $\operatorname{Spec} K \to \operatorname{Spec} R$, of $x$ followed by $g$ and $y$ followed by $g$.
--
--   This is the Néron–Ogg–Shafarevich criterion in the henselian local setting: an abelian variety over $K$ whose $\ell$-power torsion points over an algebraic closure are fixed by all inertia groups acquires an abelian-scheme model over $R$, delivered together with the cartesian comparison square and the compatibility of the two group laws on points. In this form it is the datum consumed when group-law structure is transported from the generic fibre to the model, and it is used in the treatment of fake elliptic curves and their Tate modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_abelianSchemePropertyBundle_isPullback_of_forall_specMap_comp_eq_self_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_abelianSchemePropertyBundle_isPullback_of_forall_specMap_comp_eq_self_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} (LAK : RelativeGroupLaw K gK)
    (hAK : AbelianSchemePropertyBundle K gK)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓu : IsUnit (ℓ : R))
    (hunr : ∀ (A : ValuationSubring Ω),
      (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K →
      ∀ (v : ℕ) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) gK),
        LAK.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) (ℓ ^ v) x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1) :
    ∃ (𝒜 : Scheme.{u}) (f𝒜 : 𝒜 ⟶ Spec (CommRingCat.of R)) (L𝒜 : RelativeGroupLaw R f𝒜)
      (_ : L𝒜.IsCommutative) (_ : AbelianSchemePropertyBundle R f𝒜)
      (g : AK ⟶ 𝒜) (hg : IsPullback g gK f𝒜 (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t' gK),
        (LAK.mul t' x y).1 ≫ g =
          (L𝒜.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)))
            ⟨x.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1 := by sorry
