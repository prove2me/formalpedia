-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_placeOfPoint_eq_sp_restrictAlong_of_comp_zero_of_gauss
-- name    : ModularCurve.XHDRModelAtP.placeOfPoint_eq_sp_restrictAlong_of_comp_zero_of_gauss
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/6412bfc7-6f54-5388-a7f6-bfb4f27baa51
-- title:
--   Reduction along a fibral component as Gauss specialisation of places
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb Z/M)^\times$ containing the kernel of the reduction $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$; assume $j$-invariant $q$-series `jqModC ℚ` lies in the full-level $q$-expansion field, and let $\mathfrak X$ be an `XHDRModelAtP p M H hpM hj` bundle. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : \mathrm{R}\,p \to A$ be a ring map lifting the structure map $\mathrm{R}\,p \to \overline{\mathbb Q}$. Let $\alpha$ be an integral $\overline{\mathbb Q}$-algebra map from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` into `xHFunctionFieldBar M H` which is the identity on underlying Laurent series. Let `R` be a regular prolongation of $A$ to the level-$(M/p)$ geometric function field with residue field `Fbar p M H hpM κ`, and $\mathrm{sp}$ a map from places of that function field over $\overline{\mathbb Q}$ to places of `Fbar` over $\kappa$, subject to: `R.integers` consists exactly of those $f$ admitting $x,y$ in the Laurent series over $A$ with $y$ having nonzero coefficientwise reduction and $f \cdot y = x$ after pushing coefficients to $\overline{\mathbb Q}$ (Gauss quotients); the residue of such an $f$ satisfies the corresponding identity between the coefficientwise reductions of $x$ and $y$; $\mathrm{sp}$ pushes forward, by `Finsupp.mapDomain`, the divisor of any $f \in$ `R.integers` with nonzero residue to the divisor of that residue, and is the unique such map; and every $y$ over $A$ whose image lies in the level-$(M/p)$ field is integral for `R` with residue the coefficientwise reduction of $y$. Finally let $y$ be a $\overline{\mathbb Q}$-point of $\mathfrak X.\mathrm{Meta}.C$ over the base, $u$ an $A$-point of the level-$\Gamma_M$ integral model over $\mathrm{Spec}\,\rho$ whose restriction along $A \hookrightarrow \overline{\mathbb Q}$ is $y$ transported by $\mathfrak X.\mathrm{eeta}$ followed by the first pullback projection, $u_\kappa$ a section of the fibre of that model at $\mathrm{residue} \circ \rho$ reducing $u$, and $P_0$ a closed point of $(\mathfrak X.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under $\mathfrak X.\mathrm{efib}$ followed by $\mathfrak X.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,0$ is the closed point of $u_\kappa$. Then the place of `Fbar` over $\kappa$ attached to $P_0$ by the curve model $\mathfrak X.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho$ equals $\mathrm{sp}$ applied to the restriction along $\alpha$ (the comap of the valuation subring) of the place of `xHFunctionFieldBar M H` corresponding to $y$ under $\mathfrak X.\mathrm{Meta}.\mathrm{pointEquivPlace}$.
--
--   This is the compatibility, on the component of the Deligne–Rapoport special fibre at $p \,\|\, M$ selected by the index $0$, between the geometric reduction of a point of the model of $X_H(M)$ and the specialisation of places furnished by the Gauss prolongation of the level-$(M/p)$ $q$-expansion field. It is used, together with its companion for the component indexed by $1$, in the construction of the place specialisation and prolongation data entering the component-group analysis of the fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_placeOfPoint_eq_sp_restrictAlong_of_comp_zero_of_gauss.lean

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

theorem ModularCurve.XHDRModelAtP.placeOfPoint_eq_sp_restrictAlong_of_comp_zero_of_gauss
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
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ' : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = sp ((𝔛.Meta.pointEquivPlace y).restrictAlong α hα) := by sorry
