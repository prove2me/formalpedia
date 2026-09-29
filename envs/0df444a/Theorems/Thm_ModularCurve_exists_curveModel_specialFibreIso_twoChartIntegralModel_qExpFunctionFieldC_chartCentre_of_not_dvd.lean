-- Prove2me | Theorems.Thm_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
-- name    : ModularCurve.exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/f480c18c-9bf8-5cfb-8bee-05e8bfb31f56
-- title:
--   Good reduction of the two-chart integral model at p ∤ M
-- statement:
--   Let $M \ge 1$, let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ satisfy $\Gamma_1(M) \le \Gamma \le \Gamma_0(M)$, let $p$ be a prime with $p \nmid M$, write $F =$ `qExpFunctionFieldC ℚ Γ` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios `intFormRatiosC ℚ Γ`, and let $j \in F$ be nonzero with Laurent expansion `jqModC ℚ`. Write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) $\subset \mathbb{Q}$, the subring of rationals with denominator coprime to $p$. The assertion is the existence of: for each valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ in the nonunits of $A$, a ring map $\rho_A : R \to A$ lifting the inclusion $R \hookrightarrow \overline{\mathbb{Q}}$; a `CurveModel` $M_A$ over the residue field $\kappa_A$ of $A$ for the field `qExpFunctionFieldC κ_A Γ` (an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\kappa_A$, with its function field identified with that field compatibly with the base, and with closed points in bijection with places subject to the stalk-range condition); a morphism $e_A$ from $M_A.C$ to the pullback of `TwoChartIntegralModel.toBase R F j` along $\operatorname{Spec}$ of $\kappa_A \circ \rho_A$, which is an isomorphism and satisfies $e_A$ followed by `pullback.snd` $=$ $M_A$'s structure morphism; and ring maps $\pi^{\mathrm{fin}}_A$, $\pi^{\mathrm{inf}}_A$ from the subalgebras `chartAlgFin R F j` and `chartAlgInf R F j` of $F$ to `qExpFunctionFieldC κ_A Γ`. These are required to satisfy, for every such $A$: for each $b$ in either chart algebra, there is a Laurent series $y_b$ over $A$ whose image in $\overline{\mathbb{Q}}((q))$ is the $q$-expansion of $b$ and whose coefficientwise reduction modulo the maximal ideal of $A$ is the $q$-expansion of $\pi_A(b)$; and, when $\kappa_A$ is algebraically closed, for every $\kappa_A$-point $y$ sectioning $M_A$'s structure morphism and every ring map $\beta$ from the finite (resp. infinite) chart algebra to $\kappa_A$ such that $y$ followed by $e_A$ and `pullback.fst` factors as $\operatorname{Spec}\beta$ followed by `ιFin` (resp. `ιInf`), one has $\pi_A(b) - \beta(b)$ in the nonunits of the valuation ring of the place `(Ms A hA).pointEquivPlace y` for every $b$ in that chart algebra.
--
--   This is Igusa's good-reduction theorem for the modular curve of level $M$ at a prime $p \nmid M$, in the shape: the geometric special fibre of the two-chart integral ($j$-line normalisation) model is a smooth proper model of the reduced $q$-expansion field, with the chart functions reducing coefficientwise to their $q$-expansions modulo $p$ and their values at $\kappa_A$-points controlling the associated places. It is used by the results on the model of $X_H$ at $p$ that identify places of points, distinguish cuspidal from affine places, and compare specialisation along the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd.lean

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open AlgebraicCurve
open ModularCurve

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ) :
    ∃ (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        (↥(GaloisRep.ratLocalizedAt p) →+* ↥A))
      (_ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
        A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
      (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        CurveModel (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
      (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
        (Ms A hA).C ⟶ pullback
          (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
          (Spec.map (CommRingCat.ofHom ((residue ↥A).comp (ρ A hA)))))
      (_ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p), IsIso (es A hA))
      (_ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
        es A hA ≫ pullback.snd _ _ = (Ms A hA).toBase)
      (πFin : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
        (↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j) →+* ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)))
      (πInf : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
        (↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ Γ) j) →+* ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))),
    ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
      (∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
          ↥(qExpFunctionFieldC ℚ Γ) j),
        ∃ yb : LaurentSeries ↥A,
          coeffMap A.subtype yb =
              coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ∧
            ((πFin A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) :
                LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) yb) ∧
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
          ↥(qExpFunctionFieldC ℚ Γ) j),
        ∃ yb : LaurentSeries ↥A,
          coeffMap A.subtype yb =
              coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ∧
            ((πInf A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) :
                LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) yb) ∧
      ∀ [IsAlgClosed (ResidueField ↥A)],
        (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
              q ≫ (Ms A hA).toBase = 𝟙 _})
          (β : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
              ↥(qExpFunctionFieldC ℚ Γ) j) →+* ResidueField ↥A),
          y.1 ≫ es A hA ≫ pullback.fst _ _ =
            Spec.map (CommRingCat.ofHom β) ≫
              TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
              ↥(qExpFunctionFieldC ℚ Γ) j),
            (πFin A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) -
                algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) (β b) ∈
              ((Ms A hA).pointEquivPlace y).toValuationSubring.nonunits) ∧
        (∀ (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
              q ≫ (Ms A hA).toBase = 𝟙 _})
          (β : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
              ↥(qExpFunctionFieldC ℚ Γ) j) →+* ResidueField ↥A),
          y.1 ≫ es A hA ≫ pullback.fst _ _ =
            Spec.map (CommRingCat.ofHom β) ≫
              TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j →
          ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
              ↥(qExpFunctionFieldC ℚ Γ) j),
            (πInf A hA b : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) -
                algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) (β b) ∈
              ((Ms A hA).pointEquivPlace y).toValuationSubring.nonunits) := by sorry
