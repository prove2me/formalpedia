-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_placeOfPoint_eq_delta_sp_restrictAlong_of_comp_one_of_gauss
-- name    : ModularCurve.XHDRModelAtP.placeOfPoint_eq_delta_sp_restrictAlong_of_comp_one_of_gauss
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/0c8bda8d-21e2-527d-97ae-e230aead4ffb
-- title:
--   Reduction on the component 1 as a diamond-twisted specialised place
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$ and $p^2\nmid M$, a subgroup $H\le(\mathbb Z/M)^\times$ containing every unit whose image in $(\mathbb Z/(M/p))^\times$ is $1$, with $M/p\neq0$, and assume $j$ lies in the $q$-expansion function field $\mathtt{qExpFunctionFieldC}\,\mathbb Q\,\top$; let $\mathfrak X$ be an integral model datum `XHDRModelAtP p M H hpM hj`. Let $A\subset\overline{\mathbb Q}$ be a valuation subring with $p$ a non-unit, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and $\rho:R\,p\to A$ a ring map inducing the structure map $R\,p\to\overline{\mathbb Q}$. Further data: an integral $\overline{\mathbb Q}$-algebra map $\alpha$ from the level-$(M/p)$ function field $\mathtt{xHFunctionFieldBar}(M/p)$ (for the image subgroup `infSubgroup p M H hpM`) into $\mathtt{xHFunctionFieldBar}\,M\,H$ which is the identity on underlying Laurent series; an automorphism $\theta$ of the latter field such that, for any two $\overline{\mathbb Q}$-points $y,y'$ of $\mathfrak X.\mathrm{Meta}$, equality of $y'$ followed by $\mathfrak X.\mathrm{eeta}$, $\mathtt{pullback.fst}$ and $\mathfrak X.w.\mathrm{hom}$ with $y$ followed by $\mathfrak X.\mathrm{eeta}$ and $\mathtt{pullback.fst}$ forces $\mathrm{pointEquivPlace}\,y'=\theta\cdot\mathrm{pointEquivPlace}\,y$, with $\theta\circ\alpha$ integral; a unit $\bar p$ of $\mathbb Z/(M/p)$ reducing to $p$, and the map $\delta$ on places of $\mathtt{Fbar}=\mathtt{qExpFunctionFieldC}\,\kappa\,(\Gamma_N)$ given by the semilinear action of the diamond automorphism $\mathtt{diamondActionModL}$ attached to a $\Gamma_0(M/p)$-lift of $\bar p$; a regular prolongation $R$ of the level-$(M/p)$ function field over $A$ with values in $\mathtt{Fbar}$, and a map $\mathrm{sp}$ on places, subject to: $R.\mathrm{integers}$ is the Gauss ring ($f$ lies in it iff $f\cdot y=x$ for Laurent series $x,y$ over $A$ with $y$ of nonzero reduction), $R.\mathrm{residue}$ is computed by coefficientwise reduction in that situation, $\mathrm{sp}$ pushes the divisor of any $f\in R.\mathrm{integers}$ with nonzero residue to the divisor of $R.\mathrm{residue}\,f$, $\mathrm{sp}$ is the unique such map, and every Laurent series over $A$ lying in the level-$(M/p)$ field belongs to $R.\mathrm{integers}$ with residue its coefficientwise reduction. Finally let $y$ be a $\overline{\mathbb Q}$-point of $\mathfrak X.\mathrm{Meta}$, $u$ an $A$-section of $\mathtt{toBase}\,p\,(\Gamma_M)\,hj$ over $\mathrm{Spec}\,\rho$ whose generic fibre is $y$ (via $\mathfrak X.\mathrm{eeta}$ and $\mathtt{pullback.fst}$), $u_\kappa$ a $\kappa$-point of the fibre at $\mathrm{residue}\circ\rho$ reducing $u$ and splitting $\mathtt{pullback.snd}$, and $P_0$ a closed point of $(\mathfrak X.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under $\mathfrak X.\mathrm{efib}$ followed by $\mathfrak X.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,1$ is the closed point of $u_\kappa$. Then the place attached to $P_0$ by that curve model equals $\delta\bigl(\mathrm{sp}\bigl((\mathfrak X.\mathrm{Meta}.\mathrm{pointEquivPlace}\,y)|_{\theta\circ\alpha}\bigr)\bigr)$, the restriction being the pullback of the place along $\theta\circ\alpha$.
--
--   This is the compatibility clause for the component indexed by $1$, companion to `placeOfPoint_eq_sp_restrictAlong_of_comp_zero_of_gauss`, which handles the component indexed by $0$ without the diamond twist; together they express the Eichler–Shimura congruence $T_p\equiv F+\langle p\rangle V$ at the level of places on the two components of the Deligne–Rapoport fibre at $p\parallel M$. It is used in assembling the specialisation datum that feeds the component-group and glued-specialisation package for $J_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_placeOfPoint_eq_delta_sp_restrictAlong_of_comp_one_of_gauss.lean

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

theorem ModularCurve.XHDRModelAtP.placeOfPoint_eq_delta_sp_restrictAlong_of_comp_one_of_gauss
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

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hβ : (θ.toAlgHom.comp α).IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut
      (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

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
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = δ (sp ((𝔛.Meta.pointEquivPlace y).restrictAlong (θ.toAlgHom.comp α) hβ)) := by sorry
