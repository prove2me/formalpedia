-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_frob_reduceSnd_of_isZeroSide_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.not_isAffinePlace_frob_reduceSnd_of_isZeroSide_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/87975697-7280-5938-8646-a6019e48162e
-- title:
--   Zero-side places: Frobenius of the second reading is non-affine
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ in $(\mathbb{Z}/(M/p))^\times$, with $M/p$ nonzero, and assume $jqModC\,\mathbb{Q}$ lies in the $q$-expansion function field of $SL(2,\mathbb{Z})$ over $\mathbb{Q}$. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ satisfy $A.subtype \circ \rho =$ the structure map $R\,p \to \overline{\mathbb{Q}}$. Write $F_M$ for `xHFunctionFieldBar M H`, $F_{M/p}$ for `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`. Given: a unit $pb$ of $\mathbb{Z}/(M/p)$ whose underlying element is $p$; a map $\delta$ on places of $\bar F$ acting as the semilinear automorphism attached to `diamondActionModL` at [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$ satisfying the compatibility `hwgen` with $\mathfrak{X}.w$; an $\overline{\mathbb{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$ which is the identity on Laurent expansions, with $\alpha$ and $\theta \circ \alpha$ integral; a place-specialisation datum `Psp` and a prolongation datum `Rpd` for `Psp` and $\theta$; and the component-reading hypothesis `hcomp`, which says that for each $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{X}.Meta.C$ over the base, each $A$-point $u$ of the model agreeing with $y$ after composition with `barPt A`, each $\kappa$-point $u_\kappa$ of the fibre lifting $u$ and sectioning the base, and each closed point $P_0$ of the fibre curve model $\mathfrak{X}.Mfib$ mapping under $\mathfrak{X}.efib$ followed by $\mathfrak{X}.comp\ i$ to the image of the closed point of $\kappa$ under $u_\kappa$, the place of $P_0$ equals `Psp.reduceFst α hα` applied to the place of $y$ if $i = 0$, and `Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ` applied to it if $i = 1$. Let finally $c$ be a place of $F_M$ over $\overline{\mathbb{Q}}$ lying on the zero side, i.e. $c$ satisfies `IsCuspidal'` and there are $x, x' \in F_M$ whose Laurent expansions are $jqModC\,\overline{\mathbb{Q}}$ and $qExpand\,\overline{\mathbb{Q}}\,p\,(jqModC\,\overline{\mathbb{Q}})$ respectively, together with $\tau \in A$ of residue $1$ such that $c$ takes the value $\tau$ at $x/x'^p$. Then the place $\delta(\mathrm{sp}(c|_{\theta \circ \alpha}))$ of $\bar F$, transported by `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` (restriction along the mod-$p$ Frobenius of the $q$-expansion function field), is not an affine place: there is no $x \in \bar F$ with Laurent expansion $jqModC\,\kappa$ at which that place takes a value in $\kappa$.
--
--   In the Deligne–Rapoport description of the special fibre of $X_H(M)$ at a prime $p$ exactly dividing $M$, two copies of the level-$M/p$ curve meet at the supersingular points, and a cuspidal place of the generic fibre reduces to a cusp on one of the two components. This statement records that a place on the zero side reduces, in the second of the two component readings, to a cusp even after applying the Frobenius of the reduced function field; it feeds the assembly of the cusp laws on the zero branch for prolongation data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_frob_reduceSnd_of_isZeroSide_prolongationDatum.lean

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

theorem ModularCurve.XHDRModelAtP.not_isAffinePlace_frob_reduceSnd_of_isZeroSide_prolongationDatum
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
    (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hc : (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) c) :
    ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) ((qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) ((Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) c)) := by sorry
