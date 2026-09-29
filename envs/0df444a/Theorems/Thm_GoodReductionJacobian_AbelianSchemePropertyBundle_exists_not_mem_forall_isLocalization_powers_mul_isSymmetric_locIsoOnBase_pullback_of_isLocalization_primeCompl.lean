-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/64840c6d-a2c5-51c1-b6ba-9ca385b6d5d9
-- title:
--   Spreading symmetry and the square relation from C₀ to C[1/rr']
-- statement:
--   Let $S$ be a commutative ring and $f : A \to \operatorname{Spec} S$ a morphism of schemes carrying a relative group law $L$ (a functorial group structure on $T$-points over $\operatorname{Spec} S$) and satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible (locally isomorphic to the unit), $\mathfrak p$ a prime of $S$, and $g_1 \notin \mathfrak p$. Let $C$ be an $S$-algebra and a $S[1/g_1]$-algebra, compatibly, module-finite over $S[1/g_1]$; let $C_0$ be a $C$-algebra and $S$-algebra, compatibly, which is the localisation of $C$ at the image of $S \setminus \mathfrak p$. Let $r \notin \mathfrak p$ and let $X$ be the localisation of $C$ at the image of the powers of $r$, equipped with a relative group law $L_X$ on the projection $A_X = A \times_{\operatorname{Spec} S} \operatorname{Spec} X \to \operatorname{Spec} X$ that is compatible with $L$ in the sense that for all $T$, all $t' : T \to \operatorname{Spec} X$ and all $T$-points $P,Q$ of $A_X$ over $t'$, the first projection of $L_X.\mathrm{mul}\,t'\,P\,Q$ equals the $L$-product of the first projections of $P$ and $Q$. Let $\mathcal M$ be an invertible module on $A_X$, let $\varphi : X \to C_0$ be a ring homomorphism with $\varphi \circ (C \to X) = (C \to C_0)$, let $\kappa : A_{C_0} \to A_X$ satisfy $\kappa$ followed by the first projection equals the first projection of $A_{C_0}$ and $\kappa$ followed by the second projection equals the second projection of $A_{C_0}$ followed by $\operatorname{Spec} \varphi$, and let $L_0$ be a relative group law on $A_{C_0} \to \operatorname{Spec} C_0$ compatible with $L$ in the same sense. Assume, in the sense of `LocIsoOnBase` over $\operatorname{Spec} C_0$ (for every point of the base there is an open neighbourhood $U$ such that the two modules become isomorphic after restriction to the preimage of $U$), first that $\kappa^*\mathcal M$ is symmetric, i.e. the pullback of $\kappa^*\mathcal M$ along the inversion morphism $\mathrm{negMor}$ of $L_0$ is locally isomorphic over the base to $\kappa^*\mathcal M$, and second that the pullback of $\mathcal L$ along the first projection is locally isomorphic over the base to $\kappa^*\mathcal M \otimes \mathrm{negMor}^*\kappa^*\mathcal M$. Then there exists $r' \in S$ with $r' \notin \mathfrak p$ such that for every ring $Y$ that is an $S$-algebra and a $C$-algebra, compatibly, and is the localisation of $C$ at the image of the powers of $rr'$, every ring homomorphism $\psi : X \to Y$ with $\psi \circ (C \to X) = (C \to Y)$, every $\rho : A_Y \to A_X$ compatible with the projections via $\operatorname{Spec} \psi$ exactly as $\kappa$ was, and every relative group law $L_Y$ on $A_Y \to \operatorname{Spec} Y$ compatible with $L$ in the above sense, the corresponding two conclusions hold over $\operatorname{Spec} Y$: $\rho^*\mathcal M$ is symmetric for $L_Y$, and the pullback of $\mathcal L$ along the first projection is locally isomorphic over the base to $\rho^*\mathcal M \otimes \mathrm{negMor}_{L_Y}^*\rho^*\mathcal M$.
--
--   This is a spreading-out step: two relations between invertible modules, known locally on the base over the semilocalisation $C_0$ of $C$ at $\mathfrak p$, are propagated to a single localisation $C[1/rr']$ of $C$, uniformly in the choice of such a localisation, of the transition map from $X$ and of the relative group law on it. It feeds the construction of a symmetric module on an abelian scheme satisfying the square relation, and is used by the subsequent statement producing such a module together with an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isLocalization_powers_mul_isSymmetric_locIsoOnBase_pullback_of_isLocalization_primeCompl
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (g₁ : S) (hg₁ : g₁ ∉ 𝔭.asIdeal)
    (C : Type) [CommRing C] [Algebra S C] [Algebra (Localization.Away g₁) C] [IsScalarTower S (Localization.Away g₁) C]
    (hCfin : Module.Finite (Localization.Away g₁) C)
    (C₀ : Type) [CommRing C₀] [Algebra S C₀] [Algebra C C₀] [IsScalarTower S C C₀]
    [IsLocalization (Algebra.algebraMapSubmonoid C 𝔭.asIdeal.primeCompl) C₀]
    (r : S) (hr : r ∉ 𝔭.asIdeal)
    (X : Type) [CommRing X] [Algebra S X] [Algebra C X] [IsScalarTower S C X]
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) X]
    (LX : RelativeGroupLaw X (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))))
    (hLX : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))))),
        (LX.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))).Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (φ : X →+* C₀) (hφ : φ.comp (algebraMap C X) = algebraMap C C₀)
    (κ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
    (hκ₁ : κ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
    (hκ₂ : κ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) ≫ Spec.map (CommRingCat.ofHom φ))
    (L₀ : RelativeGroupLaw C₀ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))))
    (hL₀ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C₀))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))),
        (L₀.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C₀)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (hsym : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L₀ ((Scheme.Modules.pullback κ).obj 𝓜))
    (hsq : LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C₀))))).obj 𝓛)
      ((Scheme.Modules.pullback κ).obj 𝓜 ⊗
        (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C₀)))) L₀)).obj ((Scheme.Modules.pullback κ).obj 𝓜))) :
    ∃ r' : S, r' ∉ 𝔭.asIdeal ∧
      ∀ (Y : Type) [CommRing Y] [Algebra S Y] [Algebra C Y] [IsScalarTower S C Y]
        [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers (r * r'))) Y]
        (ψ : X →+* Y) (_ : ψ.comp (algebraMap C X) = algebraMap C Y)
        (ρ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
        (_ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
        (_ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ≫ Spec.map (CommRingCat.ofHom ψ))
        (LY : RelativeGroupLaw Y (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))))
    (_ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of Y))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))),
        (LY.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S Y)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)),
        IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) LY ((Scheme.Modules.pullback ρ).obj 𝓜) ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))).obj 𝓛)
          ((Scheme.Modules.pullback ρ).obj 𝓜 ⊗
            (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) LY)).obj ((Scheme.Modules.pullback ρ).obj 𝓜)) := by sorry
