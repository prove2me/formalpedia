-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_reduceFst_eq_frob_reduceSnd_of_isZeroSide_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.reduceFst_eq_frob_reduceSnd_of_isZeroSide_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/dde09818-ea2f-564d-bf55-3f9efbb9ed66
-- title:
--   Zero-side places: first reading equals Frobenius of second reading
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial, and the hypothesis `hj` that $j(q)$ lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb{Z})$. Let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its non-units, with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : R_p \to A$ lift the structure map to $\overline{\mathbb{Q}}$. Further data: a unit $pb$ of $(\mathbb{Z}/(M/p))^\times$ reducing to $p$; a self-map $\delta$ of the places of $\bar F' = \kappa\cdot F(\Gamma_N)$ given by the semilinear action of the diamond automorphism `diamondActionModL` at level $M/p$ and group `infSubgroup p M H hpM` evaluated at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36); an $\overline{\mathbb{Q}}$-automorphism $\theta$ of $F_M = \overline{\mathbb{Q}}\cdot F(\Gamma_H(M))$ satisfying `hwgen`, which says that two $\overline{\mathbb{Q}}$-sections of $\mathfrak{X}.\mathrm{Meta}$ whose images differ by the isomorphism $\mathfrak{X}.w$ have places differing by $\theta$; an $\overline{\mathbb{Q}}$-algebra map $\alpha$ from $F_{M/p}$ to $F_M$ that is the identity on Laurent expansions, with $\alpha$ and $\theta \circ \alpha$ integral; a place-specialisation structure $\mathrm{Psp}$ with specialisation map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F'$, and a prolongation datum $\mathrm{Rpd}$ for $\mathrm{Psp}$ and $\theta$. Two compatibility hypotheses are assumed, each quantified over $i \in \{0,1\}$, a $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, a lift $u$ of $y$ to the model over $\mathrm{Spec}\,\rho$, a section $u_\kappa$ of the special fibre reducing $u$, and a closed point $P_0$ of the fibre curve model $\mathfrak{X}.\mathrm{Mfib}$ whose image under $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component map $\mathfrak{X}.\mathrm{comp}$ is the closed point hit by $u_\kappa$: `hcomp` says the place of $P_0$ is $\mathrm{sp}(W|_\alpha)$ when $i = 0$ and $\delta(\mathrm{sp}(W|_{\theta\circ\alpha}))$ otherwise, where $W$ is the place of $y$; `hcompat'` says that for $i = 0$ one has $\delta(\mathrm{sp}(W|_{\theta\circ\alpha}))$ equal to $\delta$ of the mod-$p$ Frobenius pullback of the place of $P_0$, and for $i \ne 0$ that $\mathrm{sp}(W|_\alpha)$ is the mod-$p$ Frobenius pullback of the place of $P_0$. The conclusion: for every place $W$ of $F_M$ satisfying the zero-side predicate — $W$ is cuspidal in the sense of `IsCuspidal'`, and there are $x, x' \in F_M$ with Laurent expansions $j(q)$ and $j(q^p)$ and a $\tau \in A$ of residue $1$ with $W(x/x'^p) = \tau$ — one has $\mathrm{sp}(W|_\alpha) = \varphi\big(\delta(\mathrm{sp}(W|_{\theta\circ\alpha}))\big)$, where $\varphi$ is `qExpFrobeniusPlaceModL` at level $\Gamma_N$.
--
--   This is the Eichler–Shimura congruence relation read at the cusps of the Deligne–Rapoport model of $X_H(M)$ when $p$ exactly divides $M$: a zero-side cuspidal place specialises onto the second component of the special fibre, so its first reading is the Frobenius pullback of its diamond-corrected second reading. It is used in the verification of the cusp laws for the zero and infinity sides and in the construction of the one-sided first-component data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_reduceFst_eq_frob_reduceSnd_of_isZeroSide_prolongationDatum.lean

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

theorem ModularCurve.XHDRModelAtP.reduceFst_eq_frob_reduceSnd_of_isZeroSide_prolongationDatum
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
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hz : (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) W) :
    (Psp.reduceFst α hα) W = (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) ((Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) W) := by sorry
