-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_delta_sp_restrictAlong_comp_eq_delta_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_zero
-- name    : ModularCurve.XHDRModelAtP.delta_sp_restrictAlong_comp_eq_delta_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/69fc4024-9093-50e8-8643-19acb081db53
-- title:
--   Off-diagonal reading: δ-twisted specialisation equals δ-twisted Frobenius
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and the hypothesis `hj` that `jqModC ℚ` lies in the $q$-expansion function field of $\mathrm{SL}(2,\mathbb{Z})$; let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $\alpha$ be an integral $\overline{\mathbb{Q}}$-algebra homomorphism from the level-$(M/p)$ field $\overline{F}_{M/p}$ (for the image subgroup `infSubgroup p M H hpM`) to the level-$M$ field $\overline{F}_M$ which is the identity on the underlying Laurent series, and let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{F}_M$ such that, for any two $\overline{\mathbb{Q}}$-sections $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$, if $y'$ composed with $\mathfrak{X}.\mathrm{eeta}$, the first pullback projection and $\mathfrak{X}.w.\mathrm{hom}$ agrees with $y$ composed with $\mathfrak{X}.\mathrm{eeta}$ and the first projection, then the place attached to $y'$ is the translate of the place attached to $y$ under the semilinear automorphism `SemilinearAut.ofAlgAut θ`; assume $\theta \circ \alpha$ integral. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ whose value is $p$, and let $\delta$ act on places of $\mathrm{Fbar}\,p\,M\,H\,\kappa = \overline{\kappa}$-$q$-expansion field of $\Gamma_N(p,M,H)$ by the semilinear automorphism coming from `diamondActionModL` at level $M/p$ and subgroup `infSubgroup p M H hpM`, evaluated at the lift [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) in $\Gamma_0(M/p)$. Let $R$ be a regular prolongation of $A$ from $\overline{F}_{M/p}$ to that fibre field and $sp$ a map from places of $\overline{F}_{M/p}$ over $\overline{\mathbb{Q}}$ to places of the fibre field over $\kappa$, subject to the Gauss-prolongation package summarised here: the integers of $R$ are exactly the $f$ admitting Laurent series $x, y$ over $A$ with $y$ of nonzero reduction and $f \cdot y = x$ after pushing to $\overline{\mathbb{Q}}$ (`hgauss`); the residue of such an $f$ satisfies the reduced identity coefficientwise (`hres`); $sp$ carries the divisor of any $f$ with nonzero residue to the divisor of its residue (`hdiv`), and is the unique such map (`huniq`); and every Laurent series over $A$ whose image lies in $\overline{F}_{M/p}$ lies in the integers of $R$, with residue the coefficientwise reduction (`hq`). Finally let $y$ be a $\overline{\mathbb{Q}}$-section of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$, let $u$ be an $A$-section of `toBase p (ΓM M H) hj` along `Spec.map ρ` whose restriction along `barPt A` is $y$ pushed into the generic fibre, let $u\kappa$ be a $\kappa$-point of the fibre of `toBase p (ΓM M H) hj` along the composite of $\rho$ with the residue map which is a section of the second projection and agrees with the reduction of $u$ on the first, and let $P_0$ be a closed point of the curve $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ whose image under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,0$ is the closed point of $u\kappa$. Then $\delta$ applied to the $sp$-specialisation of the place of $y$ restricted along $\theta \circ \alpha$ equals $\delta$ applied to the pullback along the mod-$p$ Frobenius on $q$-expansions of the place of $P_0$.
--
--   This is the off-diagonal entry in the table of readings of a point of the Deligne–Rapoport model of $X_H(M)$ at $p \parallel M$: the reading through $\theta \circ \alpha$, which on the relevant component is the Frobenius on places, compared after twisting both sides by the reduced diamond $\langle p \rangle$ at level $M/p$. It is used in the assembly of the place-specialisation and component-group data, `exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen`, and is obtained from the untwisted variant `sp_restrictAlong_eq_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_one`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_delta_sp_restrictAlong_comp_eq_delta_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_zero.lean

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

theorem ModularCurve.XHDRModelAtP.delta_sp_restrictAlong_comp_eq_delta_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_zero
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
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    δ (sp ((𝔛.Meta.pointEquivPlace y).restrictAlong (θ.toAlgHom.comp α) hβ)) =
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) := by sorry
