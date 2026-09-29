-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_placeOfPoint_eq_sp_restrictAlong_of_specializes_levelN_of_gauss
-- name    : ModularCurve.XHDRModelAtP.placeOfPoint_eq_sp_restrictAlong_of_specializes_levelN_of_gauss
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/3f783bde-0616-5aae-baf4-8d9c7f3ad172
-- title:
--   Place of special point as Gauss specialisation of restricted place
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, with $M/p$ nonzero, and assume $j(q)$, the Laurent series `jqModC ℚ`, lies in the $q$-expansion field `qExpFunctionFieldC ℚ ⊤`; let $\mathfrak{X}$ be a model bundle `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho \colon$ `R p` $\to A$ lift the structure map to $\overline{\mathbb{Q}}$. Let $\alpha$ be an integral $\overline{\mathbb{Q}}$-algebra map from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to `xHFunctionFieldBar M H` that is the identity on underlying Laurent series. Let $R$ be a regular prolongation of the level-$(M/p)$ field along $A$ with residue field `JHNeronObjectAtP.Fbar p M H hpM` $(\kappa)$, $\kappa$ the residue field of $A$, and let `sp` send places of the level-$(M/p)$ field over $\overline{\mathbb{Q}}$ to places of that residue field over $\kappa$. Five hypotheses describe $R$ and `sp`, summarised here: the integers of $R$ are exactly the $f$ admitting Laurent series $x, y$ over $A$ with $y$ having nonzero reduction and $f \cdot y = x$ after pushing to $\overline{\mathbb{Q}}$ (Gauss condition); the residue of such an $f$ satisfies the corresponding identity $\bar f \cdot \bar y = \bar x$ over $\kappa$; every Laurent series over $A$ lying in the level-$(M/p)$ field is integral with residue its coefficientwise reduction; `sp` pushes forward the divisor of any integral $f$ with nonzero residue to the divisor of that residue; and `sp` is the unique map with this divisor property. Finally let $y$ be a $\overline{\mathbb{Q}}$-point of $\mathfrak{X}.\mathrm{Meta}$ (a section of `𝔛.Meta.toBase`), let `xA` be an $A$-point of the level-`ΓN p M H hpM` two-chart model over `Spec.map ρ` whose generic point is the image of $y$ under `𝔛.eeta`, the first pullback projection and `𝔛.π`, let `xκ` be the corresponding section of the fibre of that model over $\kappa$ lying under `xA`, and let $P_0$ be a closed point of `(𝔛.Mfib A hA ρ hρ).C` whose image under the base map of `𝔛.efib A hA ρ hρ` is the image of the closed point of $\kappa$ under `xκ`. The conclusion is that the place of $P_0$ in the curve model `𝔛.Mfib A hA ρ hρ` equals `sp` applied to the restriction along $\alpha$ of the place of $y$ given by `𝔛.Meta.pointEquivPlace`.
--
--   This is the place-reading compatibility for the Deligne–Rapoport model at a prime exactly dividing the level: reduction of the place attached to a geometric generic point, computed through the degeneracy map to level $M/p$ and the Gauss prolongation of the $q$-expansion field, agrees with the place of the special point on the model of the special fibre. It is the component-free statement underlying the readings of places on the components of the special fibre, and is used by [`ModularCurve.XHDRModelAtP.sp_restrictAlong_eq_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_one`](thm.html#ModularCurve.XHDRModelAtP.sp_restrictAlong_eq_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_placeOfPoint_eq_sp_restrictAlong_of_specializes_levelN_of_gauss.lean

import Mathlib
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.placeOfPoint_eq_sp_restrictAlong_of_specializes_levelN_of_gauss
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

    (R : RegularProlongation A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (sp : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (hgauss : ∀ f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), f ∈ R.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (hres : ∀ (f : R.integers) (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
      (((f : R.integers) : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
      ((R.residue f : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y =
        coeffMap (IsLocalRing.residue ↥A) x)

    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
        ∀ Q, Finsupp.mapDomain sp D Q = Q.ord (R.residue f))

    (huniq : ∀ sp' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), (∀ P, D P = P.ord (f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) →
          ∀ Q, Finsupp.mapDomain sp' D Q = Q.ord (R.residue f)) → sp' = sp)

    (hq : ∀ (y : LaurentSeries ↥A)
      (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
    (hxA : barPt A ≫ xA.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1)
    (xκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hxκ : xκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ xA.1)
    (hxκ' : xκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ).base P0.1 = xκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = sp ((𝔛.Meta.pointEquivPlace y).restrictAlong α hα) := by sorry
