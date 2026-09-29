-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_away_mul_of_symmetric_principalSqrt_faithfullyFlat_atPrime
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_away_mul_of_symmetric_principalSqrt_faithfullyFlat_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/1e885e04-5ab5-5f5e-8199-c011b329670a
-- title:
--   Symmetric principal root spreads from S_𝔭 to a finite flat cover
-- statement:
--   Setting. $S$ is a commutative noetherian ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism, and $L$ a `RelativeGroupLaw S f`: a rule assigning to each $t : T \to \operatorname{Spec} S$ a multiplication, a unit and an inversion on the set `SchemeHomOver t f` of morphisms $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, subject to associativity, the two unit laws, left inverses, and naturality under base change along $\psi : T' \to T$. The hypothesis `hA` is `AbelianSchemePropertyBundle S f`, i.e. $f$ is smooth, $f$ is proper, every fibre $f^{-1}(s)$ is connected, and some relative group law on $f$ exists.
--
--   Notation and unfolded notions. For a commutative ring $B$ with an $S$-algebra structure write $A_B$ for `pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))`, with projections `pullback.fst` to $A$ and `pullback.snd` to $\operatorname{Spec} B$. For a module $M$ on a scheme $X$, `Scheme.Modules.IsInvertible M` asserts that every point of $X$ has an open neighbourhood $U$ on which the restriction of $M$ is isomorphic to the unit module of $U$. For $g : X \to \operatorname{Spec} S'$ and modules $M, M'$ on $X$, `LocIsoOnBase g M M'` asserts that every point $s$ of $\operatorname{Spec} S'$ has an open neighbourhood $U$ such that the restrictions of $M$ and $M'$ to $g^{-1}U$ are isomorphic; this is written $M \cong_{\mathrm{loc}/S'} M'$ below. For a law $L$ on $f$, `negMor f L` is the underlying morphism $A \to A$ of the inverse of the identity section, i.e. $[-1]$; `IsSymmetric` applied to $f$, $L$, $\mathcal L$ says $[-1]^*\mathcal L \cong_{\mathrm{loc}} \mathcal L$. Finally `KernelTrivial` applied to $f$, $L$, $\mathcal L$ says: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every section $x$ of $f$ over $t$, if the pullback along `sliceAt f x` of the Mumford bundle $m^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$ on $A \times_S A$ is, over the base $\operatorname{Spec} R$, locally isomorphic to the unit module, then $x$ is the unit section `L.one t`. For a law $L'$ on the structure morphism `pullback.snd` of $A_B$, the *compatibility of $L'$ with $L$* means: for every scheme $T$, every $t' : T \to \operatorname{Spec} B$ and all sections $P, Q$ of $A_B$ over $t'$, the morphism $L'.\mathrm{mul}\,t'\,P\,Q$ followed by `pullback.fst` equals the underlying morphism of $L.\mathrm{mul}$, taken over $t'$ followed by $\operatorname{Spec}$ of `algebraMap S B`, of the two sections obtained from $P$ and $Q$ by composing with `pullback.fst`.
--
--   The hypothesis `hLRC`. This is the local root-cover statement, assumed in fully quantified form: for every noetherian $S$, every $A$, every $f : A \to \operatorname{Spec} S$, every relative group law $L$ on $f$, every `AbelianSchemePropertyBundle S f`, every invertible module $\mathcal L$ on $A$, every prime $\mathfrak p$ of $S$ and every ring $W$ carrying an $S$-algebra structure and a `Localization.AtPrime 𝔭.asIdeal`-algebra structure forming a scalar tower, with $W$ faithfully flat over `Localization.AtPrime 𝔭.asIdeal`: if for every law $L'$ on $A_W$ compatible with $L$ there is an invertible module $\mathcal L_0$ on $A_W$ with `KernelTrivial`, with `IsSymmetric`, and with $(\mathrm{pullback.fst})^*\mathcal L \cong_{\mathrm{loc}/W} \mathcal L_0 \otimes [-1]^*\mathcal L_0$, then there exist $g \in S$ with $g \notin \mathfrak p$ and a ring $C$, carrying a commutative ring structure, an $S$-algebra structure and a `Localization.Away g`-algebra structure forming a scalar tower, such that $C$ is module-finite, faithfully flat and of finite presentation over `Localization.Away g`, and such that for every law $L'$ on $A_C$ compatible with $L$ there is an invertible $\mathcal L_0$ on $A_C$ with `KernelTrivial`, with `IsSymmetric`, and with $(\mathrm{pullback.fst})^*\mathcal L \cong_{\mathrm{loc}/C} \mathcal L_0 \otimes [-1]^*\mathcal L_0$.
--
--   The remaining data. A prime $\mathfrak p$ of $S$; an element $g_0 \in S$ with $g_0 \notin \mathfrak p$; an invertible module $\mathcal M$ on $A_{S_{g_0}}$, where $S_{g_0} =$ `Localization.Away g₀`; a ring $W$ with an $S$-algebra structure and a `Localization.AtPrime 𝔭.asIdeal`-algebra structure forming a scalar tower, faithfully flat over `Localization.AtPrime 𝔭.asIdeal`; a ring homomorphism $\varphi_W : S_{g_0} \to W$ with $\varphi_W \circ (\mathrm{algebraMap}\,S\,S_{g_0}) =$ `algebraMap S W`; and a morphism $\kappa : A_W \to A_{S_{g_0}}$ pinned by the two conditions $\kappa$ followed by `pullback.fst` equals `pullback.fst` of $A_W$, and $\kappa$ followed by `pullback.snd` equals `pullback.snd` of $A_W$ followed by $\operatorname{Spec}$ of $\varphi_W$.
--
--   The hypothesis `hroot`. For every relative group law $L'$ on the structure morphism of $A_W$ over $W$ which is compatible with $L$ in the above sense, there exists a module $\mathcal L_0$ on $A_W$ which is invertible, satisfies `KernelTrivial` for $L'$, satisfies `IsSymmetric` for $L'$, and satisfies $\kappa^*\mathcal M \cong_{\mathrm{loc}/W} \mathcal L_0 \otimes [-1]^*\mathcal L_0$, where $[-1]$ is `negMor` of the structure morphism of $A_W$ and $L'$.
--
--   Conclusion. There exist $s \in S$ with $s \notin \mathfrak p$; a type $C$ together with a commutative ring structure, an $S$-algebra structure, a `Localization.Away (g₀ * s)`-algebra structure and a scalar tower $S \to$ `Localization.Away (g₀ * s)` $\to C$; a ring homomorphism $\varphi : S_{g_0} \to C$ with $\varphi \circ (\mathrm{algebraMap}\,S\,S_{g_0}) =$ `algebraMap S C`; and a morphism $\pi : A_C \to A_{S_{g_0}}$ satisfying the two pinning conditions that $\pi$ followed by `pullback.fst` equals `pullback.fst` of $A_C$, and $\pi$ followed by `pullback.snd` equals `pullback.snd` of $A_C$ followed by $\operatorname{Spec}$ of $\varphi$; such that the following four assertions hold: $C$ is a finite module over `Localization.Away (g₀ * s)`; $C$ is faithfully flat over `Localization.Away (g₀ * s)`; $C$ is of finite presentation as a `Localization.Away (g₀ * s)`-algebra; and, for every relative group law $L'$ on the structure morphism of $A_C$ over $C$ which is compatible with $L$ in the sense above, there exists a module $\mathcal L_0$ on $A_C$ such that $\mathcal L_0$ is invertible, `KernelTrivial` holds for the structure morphism of $A_C$, $L'$ and $\mathcal L_0$, `IsSymmetric` holds for the same data, and $\pi^*\mathcal M \cong_{\mathrm{loc}/C} \mathcal L_0 \otimes [-1]^*\mathcal L_0$, with $[-1]$ the morphism `negMor` attached to the structure morphism of $A_C$ and $L'$.
--
--   Thus the symmetric principal root of $\mathcal M$ available over the faithfully flat $S_{\mathfrak p}$-algebra $W$ is spread out to a finite, faithfully flat, finitely presented cover $C$ of a smaller basic open neighbourhood $\operatorname{Spec} S_{g_0 s}$ of $\mathfrak p$, and the comparison morphism $\kappa$ to $A_{S_{g_0}}$ is replaced by a morphism $\pi$ subject to the same two pinning identities.
--
--   This is a spreading-out step for symmetric principal roots: a square root of $\mathcal M$ of the shape $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ with trivial kernel, known over a faithfully flat algebra over the local ring at $\mathfrak p$, is propagated to a finite faithfully flat cover of a basic open neighbourhood of $\mathfrak p$, with all data given relative to $A_{S_{g_0}}$ and a fixed comparison morphism. It is used in the construction of canonical polarisation data for fake elliptic curves, being cited by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_stage_datum`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_stage_datum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_away_mul_of_symmetric_principalSqrt_faithfullyFlat_atPrime.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_finite_faithfullyFlat_symmetric_principalSqrt_away_mul_of_symmetric_principalSqrt_faithfullyFlat_atPrime
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (hLRC : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (𝔭 : PrimeSpectrum S)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W]
    [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W] (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (hroot : (∀ (L' : RelativeGroupLaw W (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S W)))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L')).obj 𝓛₀))),
      ∃ (g : S) (_ : g ∉ 𝔭.asIdeal) (C : Type) (_ : CommRing C) (_ : Algebra S C) (_ : Algebra (Localization.Away g) C)
      (_ : IsScalarTower S (Localization.Away g) C),
      Module.Finite (Localization.Away g) C ∧ Module.FaithfullyFlat (Localization.Away g) C ∧
      Algebra.FinitePresentation (Localization.Away g) C ∧
      (∀ (L' : RelativeGroupLaw C (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C))
              (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
              (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
                (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)))
                  ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                  ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))),
                    by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
          ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C)))).Modules,
            Scheme.Modules.IsInvertible 𝓛₀ ∧
            KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
            IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
            LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))))).obj 𝓛)
              (𝓛₀ ⊗ (Scheme.Modules.pullback
                (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L')).obj 𝓛₀))))
    (𝔭 : PrimeSpectrum S)
    (g₀ : S) (hg₀ : g₀ ∉ 𝔭.asIdeal)
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))).Modules)
    (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (W : Type) [CommRing W] [Algebra S W] [Algebra (Localization.AtPrime 𝔭.asIdeal) W] [IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) W]
    (hW : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) W)
    (φW : (Localization.Away g₀) →+* W) (hφW : φW.comp (algebraMap S (Localization.Away g₀)) = algebraMap S W)
    (κ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
    (hκ₁ : κ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
    (hκ₂ : κ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))) ≫ Spec.map (CommRingCat.ofHom φW))
    (hroot : ∀ (L' : RelativeGroupLaw W (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
      (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of W))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S W))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S W))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
      ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S W)))).Modules,
        Scheme.Modules.IsInvertible 𝓛₀ ∧
        KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
        IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L' 𝓛₀ ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W))))
          ((Scheme.Modules.pullback κ).obj 𝓜)
          (𝓛₀ ⊗ (Scheme.Modules.pullback
            (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S W)))) L')).obj 𝓛₀)) :
    ∃ (s : S) (_ : s ∉ 𝔭.asIdeal) (C : Type) (_ : CommRing C) (_ : Algebra S C) (_ : Algebra (Localization.Away (g₀ * s)) C)
      (_ : IsScalarTower S (Localization.Away (g₀ * s)) C)
      (φ : (Localization.Away g₀) →+* C) (_ : φ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S C)
      (π : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
      (_ : π ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
      (_ : π ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))) ≫ Spec.map (CommRingCat.ofHom φ)),
      Module.Finite (Localization.Away (g₀ * s)) C ∧ Module.FaithfullyFlat (Localization.Away (g₀ * s)) C ∧
      Algebra.FinitePresentation (Localization.Away (g₀ * s)) C ∧
      ∀ (L' : RelativeGroupLaw C (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of C))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S C))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S C))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S C)))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧
          KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
          IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C))))
            ((Scheme.Modules.pullback π).obj 𝓜)
            (𝓛₀ ⊗ (Scheme.Modules.pullback
              (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S C)))) L')).obj 𝓛₀) := by sorry
