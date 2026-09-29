-- Prove2me | Theorems.Thm_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom
-- name    : ModularCurve.exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/6c66108c-ac72-5306-9d0b-05d1f1ba75bb
-- title:
--   Fibres of the two-chart model of X₁(M), with q-expansion readings
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \nmid M$. Write $R = \mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$, and $F =$ [`ModularCurve.x1FunctionField M`](def/ModularCurve_X1.html#L137), the intermediate field [`ModularCurve.x1FunctionFieldC ℚ M`](def/ModularCurve_X1.html#L134) $=$ `qExpFunctionFieldC ℚ (Gamma1 M)` of $\mathbb{Q} \subseteq \mathbb{Q}((q))$. Let $j \in F$ be a nonzero element whose underlying Laurent series is [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15), that is $q^{-1}$ times the integral power series `jNum` mapped into $\mathbb{Q}$ (the $q$-expansion of the modular invariant). Let $\mathfrak{Y} =$ [`AlgebraicCurve.TwoChartIntegralModel R F j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the scheme obtained as the pushout of the two affine charts, with structure morphism `TwoChartIntegralModel.toBase R F j : 𝔜 ⟶ Spec R` induced by the two structure maps $R \to$ `chartAlgFin R F j` $=$ `chartAlg R F {j}` and $R \to$ `chartAlgInf R F j` $=$ `chartAlg R F {j⁻¹}`, and with the two open immersions `ιFin` and `ιInf` from the spectra of these chart algebras. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. the image of $p$ in $\overline{\mathbb{Q}}$ lies in `Pl.nonunits`; write $\kappa =$ `IsLocalRing.ResidueField ↥Pl`. Finally let $k$ be an algebraically closed field of characteristic $p$ and $\pi_k : Pl \to k$ a ring homomorphism.
--
--   The assertion is the existence of the following data. Here `CurveModel K L` denotes a scheme $C$ together with a proper morphism $C \to \operatorname{Spec} K$ which is smooth of relative dimension $1$, $C$ integral, a ring isomorphism `ffEquiv` from $L$ onto the function field of $C$ compatible with the structure map $K \to L$ through `baseToFunctionField`, a bijection from the closed points of $C$ onto the places of $L/K$ matching stalks with valuation subrings, and the property that every finite set of points lies in one affine open. Also `coeffMap f` denotes the coefficientwise extension of a ring homomorphism $f$ to Laurent series and `coeffEmb L` $=$ `coeffMap (algebraMap ℚ L)`.
--
--   (1) A ring homomorphism $\rho_0 : R \to Pl$ with `Pl.subtype.comp ρ₀` equal to the structure map $R \to \overline{\mathbb{Q}}$, i.e. $\rho_0$ is the inclusion $\mathbb{Z}_{(p)} \subseteq Pl$ inside $\overline{\mathbb{Q}}$.
--
--   (2) A ring homomorphism $\iota : \kappa \to k$ with $\iota \circ (\text{residue map of } Pl) = \pi_k$.
--
--   (3) A curve model $M_0$ of `x1FunctionFieldC κ M` over $\kappa$, a morphism $e_0$ from $M_0.C$ to the fibre product of `TwoChartIntegralModel.toBase R F j` with $\operatorname{Spec}$ of the composite $R \to Pl \to \kappa$, the assertion that $e_0$ is an isomorphism, and the identity $e_0$ followed by the second projection $= M_0$`.toBase`; so $M_0.C \cong \mathfrak{Y} \times_{\operatorname{Spec} R} \operatorname{Spec} \kappa$ over $\operatorname{Spec}\kappa$.
--
--   (4) Two nonemptiness statements `hne₀` and `hne₀Inf`: the preimages, under $e_0$ followed by the first projection to $\mathfrak{Y}$, of the open images `ιFin ''ᵁ ⊤` and `ιInf ''ᵁ ⊤` are nonempty as schemes.
--
--   (5) Two $q$-expansion reading laws for $M_0$, one for each chart. For every $b$ in `chartAlgFin R F j` (respectively `chartAlgInf R F j`) and every Laurent series $y$ over $Pl$ whose coefficientwise image in $\overline{\mathbb{Q}}((q))$ is the $q$-expansion `coeffEmb (AlgebraicClosure ℚ)` of $b$ viewed in $F \subseteq \mathbb{Q}((q))$: transport $b$ through the inverse of `Scheme.ΓSpecIso` and the inverse of `ιFin.appIso ⊤` (resp. `ιInf.appIso ⊤`) to a section over the chart open, pull it back along $e_0$ followed by the first projection, take its germ in the function field of $M_0.C$, and transport it by $M_0$`.ffEquiv.symm` into `x1FunctionFieldC κ M`; the resulting element has Laurent series equal to `coeffMap (residue Pl) y`, the coefficientwise reduction of $y$ to $\kappa((q))$.
--
--   (6) The same package over $k$: a curve model $M_k$ of `x1FunctionFieldC k M` over $k$, a morphism $e_k$ from $M_k.C$ to the fibre product of `TwoChartIntegralModel.toBase R F j` with $\operatorname{Spec}$ of $\pi_k \circ \rho_0$, the assertion that $e_k$ is an isomorphism, the identity $e_k$ followed by the second projection $= M_k$`.toBase`, nonemptiness `hnek` and `hnekInf` of the preimages of the two chart opens under $e_k$ followed by the first projection, and the two corresponding reading laws: under the same hypothesis relating $b$ and $y$, the element of `x1FunctionFieldC k M` obtained from $b$ by pullback along $e_k$ followed by the first projection, germ, and $M_k$`.ffEquiv.symm`, has Laurent series `coeffMap πk y`.
--
--   (7) A comparison isomorphism $g$ from $M_k.C$ onto the fibre product of $M_0$`.toBase` with $\operatorname{Spec} \iota$, such that $g$ followed by the second projection is $M_k$`.toBase`, and such that $g$ followed by the first projection and then by ($e_0$ followed by the first projection to $\mathfrak{Y}$) equals $e_k$ followed by the first projection to $\mathfrak{Y}$; thus $M_k.C \cong M_0.C \times_{\operatorname{Spec}\kappa} \operatorname{Spec} k$ compatibly with the two maps to the two-chart model.
--
--   (8) A ring homomorphism $\psi :$ `x1FunctionFieldC κ M` $\to$ `x1FunctionFieldC k M` which on Laurent series is coefficientwise application of $\iota$: for every $f$ in the source, the Laurent series of $\psi(f)$ is `coeffMap ι` of the Laurent series of $f$.
--
--   The final conclusion, holding for these data, is the germ compatibility of $\psi$ with the comparison morphism: for every open $U$ of $M_0.C$ such that $U$ and its preimage under $g$ followed by the first projection are nonempty, and every section $s \in \Gamma(M_0.C, U)$, the element $M_k$`.ffEquiv.symm` of the germ, in the function field of $M_k.C$, of the pullback of $s$ along $g$ followed by the first projection, equals $\psi$ applied to $M_0$`.ffEquiv.symm` of the germ of $s$ in the function field of $M_0.C$.
--
--   This identifies the characteristic-$p$ fibres of Igusa's two-chart integral model of $X_1(M)$ over $\mathbb{Z}_{(p)}$, for $p \nmid M$: over the residue field of a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ above $p$, and over any algebraically closed field $k$ receiving $Pl$, as smooth proper models of the corresponding $q$-expansion function fields, together with the base-change comparison between the two fibres and the rule reading chart functions on both the $j$-finite and the $j$-infinite chart through their $q$-expansions. It is used by [`ModularCurve.exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom`](thm.html#ModularCurve.exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom) in the analysis of reduction of places of the modular function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem ModularCurve.exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (j : ↥(ModularCurve.x1FunctionField M)) [Fact (j ≠ 0)] (hj : ((j : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) = ModularCurve.jqModC ℚ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (πk : ↥Pl →+* k) :
    ∃ (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl) (_ : Pl.subtype.comp ρ₀ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
      (ι : (IsLocalRing.ResidueField ↥Pl) →+* k) (_ : ι.comp (IsLocalRing.residue ↥Pl) = πk)

      (M₀ : CurveModel (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M))
      (e₀ : M₀.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀))))
      (_ : IsIso e₀) (_ : e₀ ≫ pullback.snd _ _ = M₀.toBase)
      (hne₀ : Nonempty (Scheme.Opens.toScheme ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))))
      (_ : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
        (((M₀.ffEquiv.symm
            (M₀.C.germToFunctionField ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y)
      (hne₀Inf : Nonempty (Scheme.Opens.toScheme ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))))
      (_ : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
        (((M₀.ffEquiv.symm
            (M₀.C.germToFunctionField ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y)

      (Mk : CurveModel k ↥(ModularCurve.x1FunctionFieldC k M))
      (ek : Mk.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀))))
      (_ : IsIso ek) (_ : ek ≫ pullback.snd _ _ = Mk.toBase)
      (hnek : Nonempty (Scheme.Opens.toScheme ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))))
      (_ : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
        (((Mk.ffEquiv.symm
            (Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk y)
      (hnekInf : Nonempty (Scheme.Opens.toScheme ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))))
      (_ : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
        (((Mk.ffEquiv.symm
            (Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk y)

      (g : Mk.C ≅ pullback M₀.toBase (Spec.map (CommRingCat.ofHom ι)))
      (_ : g.hom ≫ pullback.snd M₀.toBase (Spec.map (CommRingCat.ofHom ι)) = Mk.toBase)
      (_ : (g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ≫ (e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) = (ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))))

      (ψ : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) →+* ↥(ModularCurve.x1FunctionFieldC k M))
      (_ : ∀ f : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M), ((ψ f : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap ι ((f : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl))),
      ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme ((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ U))] (s : Γ(M₀.C, U)),
        Mk.ffEquiv.symm (Mk.C.germToFunctionField ((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ U) (((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))).app U).hom s)) =
          ψ (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s)) := by sorry
