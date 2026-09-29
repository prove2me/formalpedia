-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_finiteMapData_ratCurveModel_igusaTo
-- name    : ModularCurve.IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/62ddac85-39d1-517a-bfb2-f1cdc54634f5
-- title:
--   Igusa's model of X₀(N₀) over ℤ₍ₚ₎, pinned
-- statement:
--   Let $N_0\ge 1$ and let $p$ be a prime with $p \nmid N_0$. Write $\mathbb{Z}_{(p)}$ for [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $p$; $F$ for `modularFunctionFieldFull N₀`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the expansions $j(q^d)$, $d \mid N_0$; $\bar F$ for `modularFunctionFieldBar N₀`, generated over $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$ by the coefficientwise images of $F$; and $A_{\mathrm{fin}}$, $A_\infty$ (`chartAlgFin`, `chartAlgInf`) for the elements of $F$ integral over $\mathbb{Z}_{(p)}[j]$, resp. $\mathbb{Z}_{(p)}[j^{-1}]$. For the structure morphism `IgusaScheme.igusaTo N₀ p` of the pushout of the two charts, the theorem asserts the simultaneous existence of: proofs that it is proper, smooth of relative dimension $1$ and geometrically integral; a $\mathbb{Z}_{(p)}$-algebra map $\varphi_\infty : A_\infty \to \mathbb{Z}_{(p)}$ given by the constant $q$-coefficient; a section $\varepsilon$ equal to $\operatorname{Spec}\varphi_\infty$ followed by the $\infty$-chart immersion `ιInf`; for every $m_0$, finite map data for $(\mathrm{igusaTo}, \varepsilon)$ of degree $m \ge m_0$ with generically étale level sets, i.e. affine opens $U, V$ with $U \sqcup V$ everything, $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(U)$, $g \in \Gamma(V)$ mutually inverse on $U \cap V = D(f) = D(g)$, with $\Gamma(U)$, $\Gamma(V)$ finite over $\mathbb{Z}_{(p)}[f]$, $\mathbb{Z}_{(p)}[g]$, every level set of $f$ over a local base free of rank $m$, and étale whenever a fixed polynomial with a unit coefficient is invertible at the level parameter; a curve model $M_\eta$ of $\bar F$ over $\overline{\mathbb{Q}}$ together with an isomorphism $e_\eta$ onto the $\overline{\mathbb{Q}}$-base change of the Igusa scheme commuting with the structure maps, such that Galois translation of $\overline{\mathbb{Q}}$-points corresponds, via `pointEquivPlace`, to the `arithmeticGalois` action on places, the preimage of the finite $j$-chart `ιFin` is nonempty, and `ffEquiv` sends each $a \in A_{\mathrm{fin}}$, taken as a germ at the generic point, to the image of its $q$-expansion under `coeffEmb`; a curve model $M_0$ of $F$ over $\mathbb{Q}$ with an isomorphism $e_0$ onto the $\mathbb{Q}$-fibre over the base, compatible with $M_\eta$ in the sense that the valuation subring of the place of a $\overline{\mathbb{Q}}$-point, pulled back along $F \to \overline{\mathbb{Q}} \otimes_{\mathbb{Q}} F \cong \bar F$, is the valuation subring of the place of the underlying closed point of $M_0$; and, for every valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $p$ is a nonunit, a ring map $\rho_A : \mathbb{Z}_{(p)} \to A$ lifting $\mathbb{Z}_{(p)} \to \overline{\mathbb{Q}}$ and a curve model $M_A$ of `modularFunctionFieldFullC` over the residue field of $A$ with an isomorphism onto the fibre along $\operatorname{Spec}$ of $\mathrm{residue} \circ \rho_A$ over the base. Finally, for each such $A$ whose residue field is algebraically closed, there is a map $r$ from places of $\bar F /\overline{\mathbb{Q}}$ to places of `modularFunctionFieldFullC` over the residue field satisfying `IsPlaceReductionModL A N₀ r` (degrees are preserved, and divisors of Laurent series with coefficients in $A$ reduce correctly), and $r$ computes specialisation: whenever an $A$-point $x_A$ of the Igusa scheme over $\operatorname{Spec}\rho_A$ induces a $\overline{\mathbb{Q}}$-point $x$ of $M_\eta$ and a residue-field point $y$ of $M_A$, the place of $y$ equals $r$ of the place of $x$.
--
--   This is the arithmetic input on Igusa's smooth proper model of $X_0(N_0)$ over $\mathbb{Z}_{(p)}$ for $p \nmid N_0$, in a named and pinned form: the cusp $\infty$ appears as the section cut out by the constant $q$-coefficient, the generic fibre models are pinned by $q$-expansions, and reduction of places modulo a valuation of $\overline{\mathbb{Q}}$ above $p$ (Deuring-style reduction) is included. It is used downstream to obtain flatness of the level model and to realise $J_0(N_0)$ with good reduction at $p$ as the Jacobian of this model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_finiteMapData_ratCurveModel_igusaTo.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_IgusaScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicCurve IsLocalRing

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_finiteMapData_ratCurveModel_igusaTo
    (N₀ : ℕ) [NeZero N₀] (p : ℕ) [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) :
    ∃ (_ : IsProper (IgusaScheme.igusaTo N₀ p))
    (_ : SmoothOfRelativeDimension 1 (IgusaScheme.igusaTo N₀ p)) (_ : GeometricallyIntegral (IgusaScheme.igusaTo N₀ p))

    (φinf : ↥(IgusaScheme.chartAlgInf N₀ p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p))
    (hφinf : ∀ x : ↥(IgusaScheme.chartAlgInf N₀ p),
      ((φinf x : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) =
        ((x : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ).coeff 0)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p)))) (IgusaScheme.igusaTo N₀ p))
    (hε : ε.1 = Spec.map (CommRingCat.ofHom φinf.toRingHom) ≫ IgusaScheme.ιInf N₀ p)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData (IgusaScheme.igusaTo N₀ p) ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale)
    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀))
    (eη : Mη.C ⟶ pullback (IgusaScheme.igusaTo N₀ p) (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) (_ : IsIso eη)
    (heη : eη ≫ pullback.snd (IgusaScheme.igusaTo N₀ p) _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N₀) g • Mη.pointEquivPlace x)

    (Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (IgusaScheme.igusaTo N₀ p)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((IgusaScheme.ιFin N₀ p) ''ᵁ ⊤))))
    (Mη_pin : ∀ a : ↥(IgusaScheme.chartAlgFin N₀ p),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField
            ((eη ≫ pullback.fst (IgusaScheme.igusaTo N₀ p)
              (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((IgusaScheme.ιFin N₀ p) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (IgusaScheme.igusaTo N₀ p)
              (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))).app
                ((IgusaScheme.ιFin N₀ p) ''ᵁ ⊤)).hom
              (((IgusaScheme.ιFin N₀ p).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ p))).inv a))))
          : ↥(modularFunctionFieldBar N₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull N₀))
    (e₀ : M₀.C ⟶ pullback (IgusaScheme.igusaTo N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) (_ : IsIso e₀)
    (he₀ : e₀ ≫ pullback.snd (IgusaScheme.igusaTo N₀ p) _ = M₀.toBase)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback (IgusaScheme.igusaTo N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) _ = x.1 ≫ eη ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull N₀))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))
    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N₀))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), (Ms A hA).C ⟶ pullback (IgusaScheme.igusaTo N₀ p) (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      es A hA ≫ pullback.snd (IgusaScheme.igusaTo N₀ p) _ = (Ms A hA).toBase),
    ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N₀),
        IsPlaceReductionModL A N₀ r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) (IgusaScheme.igusaTo N₀ p))
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x) := by sorry
