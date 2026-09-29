-- Prove2me | Theorems.Thm_ModularCurve_exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
-- name    : ModularCurve.exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/5ab1901e-92f7-5b2d-afd5-05846d1c37a4
-- title:
--   Special fibre of the two-chart integral model of X(Γ) at p ∤ M
-- statement:
--   Fix a nonzero level $M$ and a subgroup $\Gamma \le \mathrm{SL}(2,\mathbb{Z})$ with $\Gamma_1(M) \le \Gamma \le \Gamma_0(M)$, a prime $p$ with $p \nmid M$, and an element $j$ of the intermediate field $F =$ `qExpFunctionFieldC ℚ Γ` of $\mathbb{Q}((q))$ (the field generated over $\mathbb{Q}$ by the ratios `intFormRatiosC ℚ Γ`), assumed nonzero and with underlying Laurent series the $q$-expansion `jqModC ℚ`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho$ be a ring homomorphism from [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) (the subring of rationals whose denominator is coprime to $p$) to $A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Write $X$ for the two-chart integral model `TwoChartIntegralModel` of $F$ over that subring with respect to $j$, and $\iota_{\mathrm{fin}}$ for its finite chart. The assertion is that there exist a `CurveModel` over $\kappa$ with function field `qExpFunctionFieldC κ Γ` — that is, an integral scheme $M_{\mathrm{fib}}.C$ with a proper structure morphism to $\operatorname{Spec} \kappa$, smooth of relative dimension $1$, a ring isomorphism $\mathrm{ffEquiv}$ of `qExpFunctionFieldC κ Γ` with its function field over $\kappa$, a bijection of its closed points with the places of `qExpFunctionFieldC κ Γ` over $\kappa$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open — together with a morphism $e_{\mathrm{fib}}$ from $M_{\mathrm{fib}}.C$ to the fibre product of `TwoChartIntegralModel.toBase` with $\operatorname{Spec}$ of the reduction $\mathrm{res} \circ \rho$, such that $e_{\mathrm{fib}}$ is an isomorphism, the preimage under $e_{\mathrm{fib}}$ followed by the first projection of the open image of the finite chart is nonempty, $e_{\mathrm{fib}}$ followed by the second projection equals $M_{\mathrm{fib}}.\mathrm{toBase}$, and finally, for every $b$ in `chartAlgFin` (the elements of $F$ integral over the subring adjoin $j$) and every $y \in A((q))$ whose coefficientwise image in $\overline{\mathbb{Q}}((q))$ equals the image of the Laurent series of $b$, the element of `qExpFunctionFieldC κ Γ` obtained by pulling $b$ back along $e_{\mathrm{fib}}$ followed by the first projection, taking its germ at the generic point and transporting it by $\mathrm{ffEquiv}^{-1}$, has Laurent series the coefficientwise reduction of $y$ modulo the maximal ideal of $A$.
--
--   This identifies the fibre at a place of $\overline{\mathbb{Q}}$ above $p \nmid M$ of Igusa's Kroneckerian model of $X(\Gamma)$ — here realised as the two-chart integral model of the $q$-expansion function field over the rationals with denominators coprime to $p$ — with a smooth proper model of the field of reduced $q$-expansions over the residue field, pinning down the specialisation of every function on the $j$-finite chart coefficientwise. It is used in the construction of the model of $X$ at $p$ and in the analysis of the Atkin–Lehner generic chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd.lean

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

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing
open ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) :
    ∃ (Mfib : CurveModel (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
      (efib : Mfib.C ⟶ pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))))
      (_ : IsIso efib)
      (_ : Nonempty (Scheme.Opens.toScheme
        ((efib ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ''ᵁ ⊤)))),
      efib ≫ pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))) = Mfib.toBase ∧
      ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) →
        ((Mfib.ffEquiv.symm
            (Mfib.C.germToFunctionField
              ((efib ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ''ᵁ ⊤))
              (((efib ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))).app ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ''ᵁ ⊤)).hom
                (((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))).inv b))))
          : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) =
          coeffMap (residue ↥A) y := by sorry
