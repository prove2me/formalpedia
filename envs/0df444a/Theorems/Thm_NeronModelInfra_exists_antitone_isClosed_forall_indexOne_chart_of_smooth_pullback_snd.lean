-- Prove2me | Theorems.Thm_NeronModelInfra_exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd
-- name    : NeronModelInfra.exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/8fc65274-141e-59ff-9b40-7cc79dad86b4
-- title:
--   Permissible stratification of the non-smooth index-one specialisations
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), $K$ a field that is an $R$-algebra and a fraction field of $R$, and let $f\colon X\to\operatorname{Spec}R$ be a morphism of schemes that is locally of finite type and quasi-compact, whose generic fibre is smooth, in the sense that the second projection of the pullback of $f$ along $\operatorname{Spec}(\operatorname{algebraMap} R\,K)\colon \operatorname{Spec}K\to\operatorname{Spec}R$ is a smooth morphism. Call an *index-one point* a pair consisting of a discrete valuation ring $R'$ which is an $R$-algebra via a local homomorphism with $\mathfrak m_R R'=\mathfrak m_{R'}$ and with $\operatorname{ResidueField}R\to\operatorname{ResidueField}R'$ formally smooth (the predicate `IsIndexOneExtension`), together with a morphism $x\colon\operatorname{Spec}R'\to X$ whose composite with $f$ is $\operatorname{Spec}(\operatorname{algebraMap}R\,R')$; its specialisation is the image $x(\mathfrak m_{R'})$ of the closed point. Then there are $t\in\mathbb N$ and sets $Y_i\subseteq X$ ($i\in\mathbb N$) such that each $Y_i$ is closed, $Y_{i+1}\subseteq Y_i$, $Y_t=\emptyset$, every point of $Y_0$ maps to the closed point of $\operatorname{Spec}R$ and lies outside the smooth locus of $f$, and moreover: (i) the specialisation of every index-one point that does not lie in the smooth locus of $f$ lies in $Y_0$; (ii) for every $i<t$ and every index-one point whose specialisation $y$ lies in $Y_i$ but not in $Y_{i+1}$, there is an affine open $U\subseteq X$ with $y\in U$ and $U\cap Y_{i+1}=\emptyset$ such that, giving $A:=\Gamma(X,U)$ the $R$-algebra structure induced by $f$ and setting $J\subseteq A$ to be the vanishing ideal of the set of primes of $A$ corresponding to the points of $U$ lying in $Y_i$, one has: (N) any $g\in A$ such that $g\in c^{-1}(\mathfrak m_{R''})$ for every index-one extension $R''$ of $R$ and every $R$-algebra homomorphism $c\colon A\to R''$ with $J\subseteq c^{-1}(\mathfrak m_{R''})$ already lies in $J$; and for every prime $\mathfrak q$ of $A/J$ whose preimage in $A$ is the prime corresponding to $y$, both $A/J$ is smooth at $\mathfrak q$ over $\operatorname{ResidueField}R$ for every $\operatorname{ResidueField}R$-algebra structure on $A/J$ compatible with the $R$-action, and $\mathfrak q$ lies in the free locus of the $A/J$-module $(A/J)\otimes_A\Omega_{A/R}$.
--
--   This is the construction of the descending chain of closed subsets of the special fibre, with charts satisfying Bosch–Lütkebohmert–Raynaud's property (N) and the smoothness and freeness conditions, that underlies the smoothening argument in the proof of the existence of weak Néron models (Néron Models 3.4, Theorem 2, using 3.3). It is used by [`NeronModelInfra.exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd`](thm.html#NeronModelInfra.exists_hom_isIso_smoothnessDefect_add_one_le_of_smooth_pullback_snd), the inductive step lowering the smoothness defect of an index-one point by blowing up.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd.lean

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_NeronModelInfra_SmoothnessDefect

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem NeronModelInfra.exists_antitone_isClosed_forall_indexOne_chart_of_smooth_pullback_snd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hK : Smooth (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (t : ℕ) (Y : ℕ → Set X), (∀ i, IsClosed (Y i)) ∧ (∀ i, Y (i + 1) ⊆ Y i) ∧ Y t = ∅ ∧
      (∀ y ∈ Y 0, f y = IsLocalRing.closedPoint R) ∧ (∀ y ∈ Y 0, y ∉ (f.smoothLocus : Set X)) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          x.1 (IsLocalRing.closedPoint R') ∉ (f.smoothLocus : Set X) →
          x.1 (IsLocalRing.closedPoint R') ∈ Y 0) ∧
      (∀ (i : ℕ), i < t → ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
        [Algebra R R'] [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          x.1 (IsLocalRing.closedPoint R') ∈ Y i → x.1 (IsLocalRing.closedPoint R') ∉ Y (i + 1) →
          ∃ (U : X.Opens) (hU : IsAffineOpen U) (hxU : x.1 (IsLocalRing.closedPoint R') ∈ U),
            (∀ y ∈ (U : Set X), y ∉ Y (i + 1)) ∧
            letI : Algebra R Γ(X, U) :=
              ((X.presheaf.map (homOfLE le_top).op).hom.comp
                (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
            let J : Ideal Γ(X, U) :=
              PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i})

            (∀ g : Γ(X, U),
              (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
                [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
                ∀ c : Γ(X, U) →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
                  g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J) ∧

            (∀ (𝔮 : Ideal (Γ(X, U) ⧸ J)) [𝔮.IsPrime],
              𝔮.comap (Ideal.Quotient.mk J) = (hU.primeIdealOf ⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩).asIdeal →
              (∀ [Algebra (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)]
                [IsScalarTower R (IsLocalRing.ResidueField R) (Γ(X, U) ⧸ J)],
                Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮) ∧
              (⟨𝔮, ‹_›⟩ : PrimeSpectrum (Γ(X, U) ⧸ J)) ∈
                Module.freeLocus (Γ(X, U) ⧸ J) ((Γ(X, U) ⧸ J) ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]))) := by sorry
