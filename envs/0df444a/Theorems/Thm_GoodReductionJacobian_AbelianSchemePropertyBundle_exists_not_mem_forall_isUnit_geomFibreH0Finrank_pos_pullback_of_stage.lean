-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isUnit_geomFibreH0Finrank_pos_pullback_of_stage
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isUnit_geomFibreH0Finrank_pos_pullback_of_stage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/acf2a16b-e7a1-50aa-80b0-1ef69c5cefd6
-- title:
--   Fibrewise h⁰ positivity spreads from a prime to a stage
-- statement:
--   Let $S$ be a noetherian commutative ring, $A$ a scheme and $f:A\to\operatorname{Spec}S$ a morphism, equipped with a relative group law $L$ (a functorial group structure on sections of $f$ over varying bases, natural in the base) and with the bundle of properties `AbelianSchemePropertyBundle` (namely $f$ smooth, proper, with connected fibres and admitting a relative group law). Assume, as hypothesis `hPOS`, the spreading statement in fully quantified form: for every such datum over a noetherian base, every invertible module $\mathcal L$ on the total space whose Mumford bundle pulled back along a section's slice is locally trivial on the base exactly when that section is $2$-torsion for the law (the predicate `KernelIsTwoTorsion`), and every prime $\mathfrak q$, if the $k$-dimension of the global sections of the pullback of $\mathcal L$ to the geometric fibre is positive for every algebraically closed $k$ and every $S\to k$ killing nothing outside $\mathfrak q$, then some $g\notin\mathfrak q$ has this positivity at all geometric points with $g$ invertible. Fix further a prime $\mathfrak p$ of $S$, an element $g_0\notin\mathfrak p$, a ring map $\psi:S_{g_0}\to S_{\mathfrak p}$ compatible with the structure maps from $S$, and an invertible module $\mathcal M$ on the base change $A\times_{\operatorname{Spec}S}\operatorname{Spec}S_{g_0}$, such that $\mathcal M$ satisfies `KernelIsTwoTorsion` for every relative group law on the second projection whose multiplication is compatible with $L$ along the first projection, and such that the pullback of $\mathcal M$ along the canonical comparison map $A_{S_{\mathfrak p}}\to A_{S_{g_0}}$ determined by $\psi$ has positive geometric-fibre $h^0$ at every algebraically closed field $k$ and every ring map $S_{\mathfrak p}\to k$. The conclusion: there is $s\notin\mathfrak p$ such that for every commutative $S$-algebra $Y$ in which the image of $g_0s$ is a unit, every ring map $\varphi:S_{g_0}\to Y$ over $S$, every morphism $\rho:A_Y\to A_{S_{g_0}}$ commuting with the first projections and carrying the second projection of $A_Y$ to the second projection followed by $\operatorname{Spec}\varphi$, and every algebraically closed field $k$ with a ring map $Y\to k$, the geometric-fibre $h^0$ of $\rho^*\mathcal M$ is positive.
--
--   This is the spreading-out (semicontinuity) step which propagates positivity of $h^0$ on geometric fibres of a candidate polarising line bundle from the local ring at a prime to a basic open neighbourhood, in a form uniform over all $S$-algebras in which the chosen element is invertible. It is used in the construction of canonical polarisation data for fake elliptic curves, via [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_stage_datum`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_not_mem_isCanonicalPolData_away_of_stage_datum), and it cites the base-change invariance of geometric-fibre $h^0$ along cartesian squares and the stability of the abelian-scheme property bundle under base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_forall_isUnit_geomFibreH0Finrank_pos_pullback_of_stage.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_forall_isUnit_geomFibreH0Finrank_pos_pullback_of_stage
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (hPOS : (∀ {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelIsTwoTorsion f L 𝓛)
    (𝔭 : PrimeSpectrum S)
    (hpos : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      (∀ s : S, s ∉ 𝔭.asIdeal → sk s ≠ 0) → 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk),
      ∃ g : S, g ∉ 𝔭.asIdeal ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k), sk g ≠ 0 → 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk))
    (𝔭 : PrimeSpectrum S)
    (g₀ : S) (hg₀ : g₀ ∉ 𝔭.asIdeal) (ψ : Localization.Away g₀ →+* Localization.AtPrime 𝔭.asIdeal)
    (hψ : ψ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S (Localization.AtPrime 𝔭.asIdeal))
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))).Modules)
    (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (hK : ∀ (L' : RelativeGroupLaw (Localization.Away g₀) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g₀)))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        KernelIsTwoTorsion (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀))))) L' 𝓜)
    (hpos𝔭 : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : (Localization.AtPrime 𝔭.asIdeal) →+* k),
      0 < Scheme.Modules.geomFibreH0Finrank (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
        ((Scheme.Modules.pullback (pullback.lift (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ≫ Spec.map (CommRingCat.ofHom ψ))
              (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
              pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) ⟶
                pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))).obj 𝓜) k sk) :
    ∃ s : S, s ∉ 𝔭.asIdeal ∧
      ∀ (Y : Type) [CommRing Y] [Algebra S Y] (_ : IsUnit (algebraMap S Y (g₀ * s)))
        (φ : (Localization.Away g₀) →+* Y) (_ : φ.comp (algebraMap S (Localization.Away g₀)) = algebraMap S Y)
        (ρ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))))
        (_ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
        (_ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g₀)))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ≫ Spec.map (CommRingCat.ofHom φ))
        (k : Type) [Field k] [IsAlgClosed k] (sk : Y →+* k),
        0 < Scheme.Modules.geomFibreH0Finrank (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) ((Scheme.Modules.pullback ρ).obj 𝓜) k sk := by sorry
