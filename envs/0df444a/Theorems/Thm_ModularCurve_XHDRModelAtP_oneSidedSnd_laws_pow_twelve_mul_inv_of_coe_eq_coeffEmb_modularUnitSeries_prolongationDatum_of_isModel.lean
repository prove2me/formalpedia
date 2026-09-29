-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
-- name    : ModularCurve.XHDRModelAtP.oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/564b7a62-d02e-58e2-a728-b936b43f302d
-- title:
--   One-sided second laws for p¹²u⁻¹ on a Deligne–Rapoport model
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$, $p^2 \nmid M$, and a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb Z/(M/p))^\times$; let $hj$ record that the $q$-expansion `jqModC` of $j$ lies in the level-$\top$ $q$-expansion function field over $\mathbb Q$, and let $\mathfrak X$ be a Deligne–Rapoport model datum `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : R_p \to A$ lift the structural map $R_p \to \overline{\mathbb Q}$. Write $F_M =$ `xHFunctionFieldBar M H`, $F_{M/p}$ for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM`, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM` $\kappa$. Let $pb$ be a unit of $\mathbb Z/(M/p)$ whose value is $p$, and let $\delta$ act on places of $\bar F$ as the semilinear automorphism attached to the diamond automorphism `diamondActionModL` at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Let $\theta$ be a $\overline{\mathbb Q}$-algebra automorphism of $F_M$ and $\alpha : F_{M/p} \to F_M$ a $\overline{\mathbb Q}$-algebra map, with $\alpha$ and $\theta \circ \alpha$ integral; let $Psp$ be a place-specialisation datum `JHPlaceSpecialization p M H hpM A` and $Rpd$ a `ProlongationDatum` for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with values in $\bar F$ linked by $f \in R_2 \iff \theta f \in R_1$ and matching residues. Assume: $hwgen$, that $\theta$ induces the Atkin–Lehner involution $\mathfrak X.w$ on $\overline{\mathbb Q}$-points of the curve model $\mathfrak X.\mathrm{Meta}$ via `pointEquivPlace`; $h\theta$, that if $f \in F_M$ and $v \in F_{M/p}$ have the same Laurent series then $\theta f$ has Laurent series $q \mapsto q^p$ applied to it; $h\alpha_{coe}$, that $\alpha$ preserves Laurent series; the type dichotomy $hTD$ for $\alpha$, $\theta \circ \alpha$, $\delta$, asserting for every place $W$ of $F_M$ that either $\mathrm{red}_1 W$ is the mod-$p$ Frobenius place of $\mathrm{red}_2 W$ or $\delta$ of the Frobenius place of $\mathrm{red}_1 W$ is $\mathrm{red}_2 W$, where $\mathrm{red}_1 W = Psp.\mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2 W = \delta(Psp.\mathrm{sp}(W|_{\theta \circ \alpha}))$; and $hmodel$, that $Rpd$ is a model for these data (the two divisor laws and the two cusp laws). Two further hypotheses, summarised here, state for each of the two components $i \in \mathrm{Fin}\,2$ of the fibre how the place attached by $\mathfrak X.\mathrm{Mfib}$ to a closed point $P_0$ lying over the image of a $\kappa$-point is computed from $\mathrm{red}_1$ or $\mathrm{red}_2$ of the place of the corresponding generic point $y$, and the Frobenius-twisted form of this comparison. Finally let $u \in F_M$ have Laurent series the coefficientwise image in $\overline{\mathbb Q}$ of Ogg's modular unit series `modularUnitSeries p` $= \Delta(q)/\Delta(q^p)$, put $u_2 = p^{12} u^{-1}$, assume $u_2$ lies in the valuation subring $R_2.\mathrm{integers}$, and let $D_2$ be the divisor with $D_2(W) = \mathrm{ord}_W(u_2)$ for every place $W$ of $F_M$. The conclusion is the conjunction of two statements about the residue $\bar u_2 = R_2.\mathrm{residue}\,u_2 \in \bar F$: first, for every place $v$ of $\bar F$ not satisfying `JHPlaceSpecialization.Fixed` for $\delta$ (that is, with $\mathrm{Frob}_p(\delta(\mathrm{Frob}_p(v))) \ne v$), the pushforward along $\mathrm{red}_2$ of the restriction of $D_2$ to the places satisfying `JHPlaceSpecialization.IsStrictSnd` takes the value $\mathrm{ord}_v(\bar u_2)$ at $v$; second, for every place $C$ of $F_M$ satisfying `JHPlaceSpecialization.IsZeroSide` (that is, $C$ satisfies `IsCuspidal'` and there are $x, x' \in F_M$ with Laurent series `jqModC` and its $q \mapsto q^p$ substitute, and a $\tau \in A$ with residue $1$ such that $C$ takes the value $\tau$ at $x/x'^p$), the pushforward along $\mathrm{red}_2$ of the restriction of $D_2$ to the zero-side places takes the value $\mathrm{ord}_{\mathrm{red}_2 C}(\bar u_2)$ at $\mathrm{red}_2 C$.
--
--   This is the second-side half of the divisor bookkeeping for the Atkin–Lehner transform $p^{12}u^{-1}$ of Ogg's modular unit $\Delta(q)/\Delta(q^p)$ on the Deligne–Rapoport model of $X_H$ at $p$: the pushforward of its divisor along the second reduction map agrees with the order function of its residue in the special fibre, both away from the $\delta$-fixed places and along the zero-side cuspidal places. It feeds the construction of the unit pair and jump data in [`ModularCurve.XHDRModelAtP.exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw`](thm.html#ModularCurve.XHDRModelAtP.exists_unit_pair_divisor_oneSidedLaws_jump_prolongationDatum_of_isModel_of_nodeValueLaw), which is where the character-group computation at the supersingular fibre is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel.lean

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

theorem ModularCurve.XHDRModelAtP.oneSidedSnd_laws_pow_twelve_mul_inv_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
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
    (u₂ : ↥(xHFunctionFieldBar M H))
    (hu₂ : u₂ = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((p : ℕ) : AlgebraicClosure ℚ) ^ 12) * u⁻¹)
    (h₂ : u₂ ∈ Rpd.R₂.integers)
    (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD₂ : ∀ W, D₂ W = W.ord u₂) :
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) := by sorry
