-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_sp_restrictAlong_eq_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_one
-- name    : ModularCurve.XHDRModelAtP.sp_restrictAlong_eq_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/77cabf97-8a01-5edb-aeba-72cd839417a3
-- title:
--   Frobenius reading of the π-specialisation on the 0-component
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial, and the hypothesis `hj` that the $q$-series `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`; let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`. Let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p$ a nonunit of $A$, with residue field $\kappa$ of characteristic $p$ and algebraically closed, and $\rho : R p \to A$ a ring map whose composite with $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Let $\alpha$ be an integral $\overline{\mathbb{Q}}$-algebra map from $F' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to $F =$ `xHFunctionFieldBar M H` which is the identity on the underlying Laurent series, let $R$ be a `RegularProlongation` of $F'$ over $A$ with residue field $\bar F =$ `qExpFunctionFieldC κ (ΓN p M H hpM)` (a valuation subring `R.integers` of $F'$ contracting to $A$, with surjective residue map onto $\bar F$ whose kernel is the maximal ideal), and let $sp$ send places of $F'$ over $\overline{\mathbb{Q}}$ to places of $\bar F$ over $\kappa$. The hypotheses `hgauss`, `hres`, `hdiv`, `huniq`, `hq`, summarised here, say: membership in `R.integers` is the Gauss condition that $f$ times some Laurent series over $A$ with nonzero reduction is again a Laurent series over $A$; `R.residue` is computed by coefficientwise reduction in such a presentation; `Finsupp.mapDomain sp` carries the divisor of any $f \in$ `R.integers` with nonzero residue to the order divisor of `R.residue f`, and $sp$ is the unique map with that property; and every Laurent series over $A$ lying in $F'$ is in `R.integers` with residue its coefficientwise reduction. Finally let $y$ be a $\overline{\mathbb{Q}}$-point of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, $u$ a section of `toBase p (ΓM M H) hj` over `Spec.map ρ` whose base change along $A \hookrightarrow \overline{\mathbb{Q}}$ agrees with $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first pullback projection, $u_\kappa$ a $\kappa$-point of the fibre of `toBase p (ΓM M H) hj` at `residue ∘ ρ` which is a section of that fibre and reduces $u$, and $P_0$ a closed point of $(\mathfrak{X}.\mathrm{Mfib}\ A\ hA\ \rho\ h\rho).C$ whose image under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\ \dots\ 1$ is the closed point of $u_\kappa$. Then $sp$ of the restriction along $\alpha$ of the place of $F$ attached to $y$ by $\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}$ equals `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` applied to the place of $\bar F$ attached to $P_0$, i.e. the restriction of that place along the $p$-power Frobenius map of $\bar F$.
--
--   This is the entry of the table of specialisation readings corresponding to a point of $X_H(M)$, with $p \parallel M$, whose reduction lies on the component indexed by $1$: there the degeneracy map $\pi$ induces the Frobenius on places, so the Deuring-type specialisation along $\alpha = \pi^*$ of the place of a $\overline{\mathbb{Q}}$-point is the Frobenius twist of the place of its reduction. It feeds the companion off-diagonal statement on the zero component and the construction of the glued specialisation data used for the component-group computation on the Deligne–Rapoport model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_sp_restrictAlong_eq_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_one.lean

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

theorem ModularCurve.XHDRModelAtP.sp_restrictAlong_eq_qExpFrobeniusPlaceModL_placeOfPoint_of_comp_one
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
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) :
    sp ((𝔛.Meta.pointEquivPlace y).restrictAlong α hα) =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0) := by sorry
