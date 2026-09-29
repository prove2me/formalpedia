-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/22ca90de-379a-5be8-a8a3-cb5eebe2c0d6
-- title:
--   Very ampleness by sections from geometric fibres
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, and $f : A \to \operatorname{Spec} S$ a morphism carrying the property bundle `AbelianSchemePropertyBundle` (that is, $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law over $S$ for $f$ exists). Let $M$ be an $\mathcal O_A$-module which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $M$ is isomorphic to the unit module sheaf of $U$. Assume: (i) for every algebraically closed field $k$ and every ring homomorphism $sk : S \to k$, the pullback of $M$ to $A \times_{\operatorname{Spec} S} \operatorname{Spec} k$ along the first projection satisfies `ClosedImmersionBySections` over $\operatorname{Spec} k$, i.e. admits a projective presentation (finitely many global sections $\sigma_0,\dots,\sigma_N$, together with a morphism to the Proj of the polynomial ring over $k$ in $N+1$ variables, compatible with the structure map and frame by frame with the $\sigma_i$) whose morphism to projective space is a closed immersion; (ii) $\Gamma(M,\top)$ is a finite and projective module over $S$, acting through the structure map of $f$; (iii) for every ring homomorphism $\varphi : S \to S'$ and every cartesian square given by $g_A : A' \to A$ over $\operatorname{Spec}\varphi$, there is an $S'$-linear isomorphism $S' \otimes_S \Gamma(M,\top) \cong \Gamma(g_A^{*}M, g_A^{-1}\top)$ sending $s' \otimes \tau$ to $s' \cdot g_A^{*}\tau$, where $g_A^*\tau$ is the canonical pulled-back local section. Then `ClosedImmersionBySections` holds for $M$ and $f$: there are an $N$ and a projective presentation of $M$ over $\operatorname{Spec} S$ by $N+1$ global sections whose associated morphism $A \to \mathbb P^N_S$ is a closed immersion. Of the hypotheses, the proof uses only properness from the property bundle and only the finiteness half of (ii).
--
--   This is the descent of relative very ampleness (in the concrete form: a closed immersion into $\mathbb P^N_S$ cut out by global sections) from the geometric fibres to the whole family, under finiteness of the module of global sections and compatibility of sections with base change. It is used in the construction of projective embeddings of the fake elliptic curves, for the third and fourth tensor powers of a canonical polarisation over a Noetherian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open AlgebraicGeometry

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      Scheme.Modules.ClosedImmersionBySections
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M)
        (pullback.snd f (Spec.map (CommRingCat.ofHom sk))))
    (hfg : letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
      Module.Finite S Γ(M, ⊤) ∧ Module.Projective S Γ(M, ⊤))
    (hbc : ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
        (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A)
        (hg : CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ))),
        letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
        letI : Module S' Γ((Scheme.Modules.pullback gA).obj M, gA ⁻¹ᵁ ⊤) :=
          Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top).hom
        letI : Algebra S S' := φ.toAlgebra
        ∃ e : S' ⊗[S] Γ(M, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj M, gA ⁻¹ᵁ ⊤),
          ∀ (s' : S') (τ : Γ(M, ⊤)), e (s' ⊗ₜ[S] τ) = s' • Scheme.Modules.pullbackLocalSection gA τ) :
    Scheme.Modules.ClosedImmersionBySections M f := by sorry
