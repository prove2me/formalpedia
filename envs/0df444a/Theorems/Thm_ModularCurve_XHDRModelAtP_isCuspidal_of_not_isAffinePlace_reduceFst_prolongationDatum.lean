-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isCuspidal_of_not_isAffinePlace_reduceFst_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.isCuspidal_of_not_isAffinePlace_reduceFst_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/581ed261-3829-56c8-bfa0-f0100c2f260e
-- title:
--   Non-affine first reduction forces a cuspidal place
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and assume $M/p \neq 0$ and that $j$, as the Laurent series `jqModC ℚ`, lies in the $q$-expansion function field of the full group $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ and with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : R_p \to A$ lift the structure map $R_p \to \overline{\mathbb{Q}}$. Write $F_M =$ `xHFunctionFieldBar M H`, $F_{M/p} =$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`. Further data: a unit $pb$ of $\mathbb{Z}/(M/p)$ with underlying value $p$; the operator $\delta$ on places of $\bar F$ given by the action of the semilinear automorphism attached to `diamondActionModL` evaluated at [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); an automorphism $\theta$ of $F_M$ over $\overline{\mathbb{Q}}$ which, by `hwgen`, computes the effect on places of $\mathfrak{X}.w$ on $\overline{\mathbb{Q}}$-sections of $\mathfrak{X}.\mathrm{Meta}$; an $\overline{\mathbb{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$ which is the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral; a place-specialisation datum $Psp$ from places of $F_{M/p}$ to places of $\bar F$, a prolongation datum $Rpd$ for $Psp$ and $\theta$, and a compatibility clause `hcomp` asserting, for $i \in \{0,1\}$ and matching sections, points and fibre data (summarised here), that the place of the relevant closed point of the fibre curve model is $Psp.\mathrm{reduceFst}\,\alpha$ applied to the place of $y$ when $i = 0$, and $Psp.\mathrm{reduceSnd}\,(\theta \circ \alpha)\,\delta$ applied to it otherwise. The conclusion: if $W$ is a place of $F_M$ over $\overline{\mathbb{Q}}$ such that $Psp.\mathrm{reduceFst}\,\alpha\,W = Psp.\mathrm{sp}(W|_\alpha)$ is not affine, i.e. there is no $x \in \bar F$ with Laurent expansion `jqModC κ` and no $a \in \kappa$ at which that place takes the value $a$ on $x$, then $W$ is cuspidal: for every $x \in F_M$ whose Laurent expansion is `jqModC` $\overline{\mathbb{Q}}$ and every $a \in A$, one has $\mathrm{ord}_W(x - a) \le 0$.
--
--   This is the $\Gamma_H$-level form of the statement that a place of $X_H(M)$ whose reduction along the first degeneracy map fails to have a finite $j$-value must itself be a cusp, read off the special fibre of the Deligne–Rapoport model at a prime exactly dividing the level. It feeds the cusp laws and local semicontinuity statements for the two components of the special fibre, via the two compatibility readings $\mathrm{reduceFst}$ and $\mathrm{reduceSnd}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isCuspidal_of_not_isAffinePlace_reduceFst_prolongationDatum.lean

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

theorem ModularCurve.XHDRModelAtP.isCuspidal_of_not_isAffinePlace_reduceFst_prolongationDatum
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
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hW : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) ((Psp.reduceFst α hα) W)) :
    (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) W := by sorry
