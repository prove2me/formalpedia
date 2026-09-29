-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_cuspLawZero_prolongationDatum_offDiag
-- name    : ModularCurve.XHDRModelAtP.cuspLawZero_prolongationDatum_offDiag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/4f4f4666-6580-50d8-a942-06aff99f04f6
-- title:
--   Zero-side cusp law for the Deligne–Rapoport prolongation datum
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and the hypothesis $hj$ that the $q$-expansion $j$-series `jqModC ℚ` lies in $q$-expansion function field of $\mathrm{SL}_2(\mathbb{Z})$ over $\mathbb{Q}$. Let $\mathfrak{X}$ be a Deligne–Rapoport datum `XHDRModelAtP p M H hpM hj` (a proper flat integral normal model of $X_H(M)$ over $R_p$, its smooth model at the auxiliary level, a curve model `Meta` over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H`, and the associated fibre data), let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p$ a nonunit of $A$ whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ lift the structure map $R_p \to \overline{\mathbb{Q}}$. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and let $\delta$ be the map on places of $\mathrm{Fbar} =$ the $q$-expansion function field of $\Gamma_N(p,M,H)$ over $\kappa$ given by the semilinear action of the reduced diamond automorphism `diamondActionModL` at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H`, assumed via $hwgen$ to implement the map $\mathfrak{X}.w$ on points of `Meta.C`: whenever two $\overline{\mathbb{Q}}$-sections $y, y'$ satisfy that $y'$ followed by $\mathfrak{X}.eeta$, the first pullback projection and $\mathfrak{X}.w.hom$ equals $y$ followed by $\mathfrak{X}.eeta$ and the first projection, the associated places satisfy $\mathrm{place}(y') = \theta \cdot \mathrm{place}(y)$. Let $\alpha$ be a $\overline{\mathbb{Q}}$-algebra map from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` into `xHFunctionFieldBar M H` which is the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral. Let $Psp$ be a place specialisation `JHPlaceSpecialization p M H hpM A` and $Rpd$ a prolongation datum for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ in `xHFunctionFieldBar M H` with values in $\mathrm{Fbar}$ such that $R_2$-integrality is $\theta$-pullback of $R_1$-integrality and $R_2$-residues are $R_1$-residues of $\theta$-images. Assume: the $R_2$-residue of $\alpha v$ is the mod-$p$ Frobenius `qExpFrobeniusModL` of its $R_1$-residue, for all $v$ in the smaller function field; the diagonal reading law $hcomp$, saying that for $i \in \{0,1\}$ and compatible data (a $\overline{\mathbb{Q}}$-section $y$ of `Meta`, a lift $u$ over $\mathrm{Spec}\,\rho$, a residue-field section $u\kappa$ of the fibre, and a closed point $P_0$ of the fibre curve model whose image under $\mathfrak{X}.efib$ followed by the $i$-th component map is the closed point of $u\kappa$) the place of $P_0$ equals $Psp.\mathrm{reduceFst}\,\alpha$ of the place of $y$ for $i = 0$ and $Psp.\mathrm{reduceSnd}\,(\theta \circ \alpha)\,\delta$ of it for $i = 1$; and the off-diagonal law $hcompat'$, saying that under the same data the cross readings hold, namely $Psp.\mathrm{reduceSnd}\,(\theta\circ\alpha)\,\delta$ of the place of $y$ equals $\delta$ applied to the Frobenius place `qExpFrobeniusPlaceModL` of the place of $P_0$ when $i = 0$, and $Psp.\mathrm{reduceFst}\,\alpha$ of the place of $y$ equals that Frobenius place when $i = 1$. The conclusion is `Rpd.CuspLawZero (θ.toAlgHom.comp α) hβ δ`: for every $f$ in `xHFunctionFieldBar M H` lying in the integers of both $R_1$ and $R_2$ with both residues nonzero, every divisor $D$ with $D(W) = \mathrm{ord}_W f$ at every place $W$, and every place $c$ satisfying `IsZeroSide`, the pushforward along $W \mapsto \delta(Psp.sp(W|_{\theta\circ\alpha}))$ of the part of $D$ supported on `IsZeroSide` places, evaluated at the image of $c$, equals the order of the $R_2$-residue of $f$ at that image.
--
--   This is the cusp law on the zero-side cuspidal family for the second reading of the prolongation datum: the local computation of divisors at the cusps lying over the $0$-component of the Deligne–Rapoport fibre at $p \parallel M$, with the second reading twisted by the reduced diamond $\langle \bar p\rangle$. It is one of the conjuncts of the model law assembled by [`ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen), which exports the glued specialisation and component-group data used in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_cuspLawZero_prolongationDatum_offDiag.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.cuspLawZero_prolongationDatum_offDiag
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
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (hcomp : (∀ (i : Fin 2)
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
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))

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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    Rpd.CuspLawZero (θ.toAlgHom.comp α) hβ δ := by sorry
