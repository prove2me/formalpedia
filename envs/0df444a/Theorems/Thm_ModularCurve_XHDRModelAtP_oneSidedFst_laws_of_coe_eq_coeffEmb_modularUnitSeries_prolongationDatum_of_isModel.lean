-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
-- name    : ModularCurve.XHDRModelAtP.oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/9b3b2053-77a6-53cc-a387-ff671da5a30d
-- title:
--   One-sided first laws for the modular unit Δ(q)/Δ(qᵖ)
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, the hypothesis $j(q) \in$ `qExpFunctionFieldC ℚ ⊤`, and a model $\mathfrak X$ of type `XHDRModelAtP p M H hpM hj`. Let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p$ in its non-units, with algebraically closed residue field $\kappa$ of characteristic $p$, and $\rho : R_p \to A$ a ring map inducing the structure map $R_p \to \overline{\mathbb{Q}}$. Let $\mathrm{pb}$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and let $\delta$ act on places of $\mathrm{Fbar} =$ `qExpFunctionFieldC κ (ΓN p M H hpM)` by the diamond automorphism `diamondActionModL` at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Further data: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M =$ `xHFunctionFieldBar M H`, an integral $\overline{\mathbb{Q}}$-algebra map $\alpha$ from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to $F_M$ with $\theta \circ \alpha$ integral, a place-specialization datum $\mathrm{Psp}$ and a prolongation datum $\mathrm{Rpd}$ for $\mathrm{Psp}$ and $\theta$. The hypotheses, summarised here, comprise: a genericity clause identifying $\mathfrak X.\mathrm{Meta}$-points related by $\mathfrak X.w$ with the $\theta$-translate of places; that $\theta$ realises $q \mapsto q^p$ on $q$-expansions (`qExpand`) while $\alpha$ preserves them; the type dichotomy `Psp.TypeDichotomy`; `Rpd.IsModel` (the two divisor laws and the two cusp laws) for $\alpha$, $\theta \circ \alpha$, $\delta$; and two compatibility clauses, for each of the two components $i \in \mathrm{Fin}\,2$, equating the place of a closed point of the fibre model $\mathfrak X.\mathrm{Mfib}$ with `Psp.reduceFst` or `Psp.reduceSnd` of the place of the corresponding $\overline{\mathbb{Q}}$-point, respectively with their `qExpFrobeniusPlaceModL`-twists. Finally let $u \in F_M$ have $q$-expansion the image under `coeffEmb` of `modularUnitSeries p`, lie in the valuation subring $\mathrm{Rpd}.R_1.\mathrm{integers}$, and let $D$ be the divisor $W \mapsto \mathrm{ord}_W(u)$. The conclusion is twofold: first, for every place $v$ of $\mathrm{Fbar}$ over $\kappa$ that is not `Fixed` for $\delta$, the pushforward along `Psp.reduceFst α hα` of the restriction of $D$ to the strict-first places, evaluated at $v$, equals $\mathrm{ord}_v$ of the residue $\mathrm{Rpd}.R_1$ assigns to $u$; second, for every place $C$ of $F_M$ over $\overline{\mathbb{Q}}$ satisfying `IsInftySide`, the pushforward along `Psp.reduceFst α hα` of the restriction of $D$ to the $\infty$-side places, evaluated at `Psp.reduceFst α hα C`, equals the order of that same residue of $u$ at `Psp.reduceFst α hα C`.
--
--   This records the two first-component laws satisfied by the divisor of the modular unit $\Delta(q)/\Delta(q^p)$ when it is specialised from the function field of $X_H(M)$ to the characteristic-$p$ fibre, in the setting of the Deligne–Rapoport model at a prime exactly dividing the level. It is used in the assembly of the modular-unit input to the level-lowering argument, alongside the companion statement for the second component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

open Classical in

theorem ModularCurve.XHDRModelAtP.oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (u : ↥(xHFunctionFieldBar M H))
    (hu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p))
    (h₁ : u ∈ Rpd.R₁.integers)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD : ∀ W, D W = W.ord u) :
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) v = v.ord (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) := by sorry
