-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffinePlace_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffinePlace_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/6e952246-7f41-5b03-adb6-04ff821b4c51
-- title:
--   Both cuspidal sides lie above a non-affine place
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$, and assume $j$, as a Laurent series, lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb{Z})$ over $\mathbb{Q}$. Let $\mathfrak{X}$ be a model datum `XHDRModelAtP` for level $\Gamma_H(M)$ at $p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ lift the structure map to $\overline{\mathbb{Q}}$. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ reducing to $p$, let $\delta$ be a self-map of the places of $\bar F = \kappa \cdot F(\Gamma_N)$, let $\theta$ be an $\overline{\mathbb{Q}}$-automorphism of $F_M = \overline{\mathbb{Q}} \cdot F(\Gamma_H(M))$ satisfying `hwgen` for the involution $\mathfrak{X}.w$, and let $\alpha : F_{M/p} \to F_M$ be an $\overline{\mathbb{Q}}$-algebra map preserving $q$-expansions, with $\alpha$ and $\theta \circ \alpha$ integral. Let `Psp` be a place-specialisation datum, with specialisation map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$, and `Rpd` a prolongation datum for $\mathrm{Psp}$ and $\theta$. Assume `hcomp`: for each $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-section $y$ of $\mathfrak{X}.\mathrm{Meta}$, each section $u$ of the level-$\Gamma_H(M)$ model over $\mathrm{Spec}\,\rho$ whose base change to $\overline{\mathbb{Q}}$ is $y$, each $\kappa$-point $u_\kappa$ of the fibre compatible with $u$ through the residue map, and each closed point $P_0$ of the special-fibre curve model whose image under $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component map is the closed point of $u_\kappa$, the place of $P_0$ equals $\mathrm{sp}(\mathrm{pointEquivPlace}(y)|_\alpha)$ when $i = 0$ and $\delta\bigl(\mathrm{sp}(\mathrm{pointEquivPlace}(y)|_{\theta \circ \alpha})\bigr)$ when $i = 1$. Finally let $u$ be a place of $\bar F$ such that its Frobenius pullback $\varphi(u)$ is not an affine place, i.e. no element of $\bar F$ with $q$-expansion $j$ has a value in $\kappa$ at $\varphi(u)$. The conclusion is twofold: there is a place $c$ of $F_M$ on the $\infty$-side (cuspidal, with elements $x, x'$ of $F_M$ of $q$-expansions $j(q)$ and $j(q^p)$ and a value of $x'/x^p$ at $c$ of residue $1$) with $\mathrm{sp}(c|_\alpha) = \varphi(u)$; and there is a place $c$ on the $0$-side (satisfying the companion cuspidality predicate, with a value of $x/x'^p$ of residue $1$) with $\delta(\mathrm{sp}(c|_{\theta \circ \alpha})) = u$.
--
--   This is the surjectivity half of the cusp bookkeeping on the Deligne–Rapoport model of $X_H(M)$ at a prime exactly dividing the level: every place of the special-fibre function field that is not affine (not in the locus where $j$ specialises) is reached both by an $\infty$-side cusp of $X_H(M)_{\overline{\mathbb{Q}}}$ under the first reading and by a $0$-side cusp under the second reading. It feeds the cusp-law assemblies that compare the two components, via the statements on prolongation data and on the glued specialisation with its off-diagonal component-group behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffinePlace_prolongationDatum.lean

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

theorem ModularCurve.XHDRModelAtP.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffinePlace_prolongationDatum
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
    (u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hu : ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) ((qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) u)) :
    (∃ c, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceFst α hα) c = (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) u) ∧ (∃ c, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) c = u) := by sorry
