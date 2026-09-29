-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_lift_regular_section_comp_zero_ord_placeOfPoint_eq_one_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.exists_lift_regular_section_comp_zero_ord_placeOfPoint_eq_one_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/57798c88-5f47-5f64-b2fb-43aeb9948071
-- title:
--   A level-M/p lift uniformising a fibre place along cuspidal sections
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit that reduces to $1$ modulo $M/p$, and $j$-data $hj$ expressing that $jqModC\ \mathbb Q$ lies in the level-one $q$-expansion field; let $\mathfrak X$ be an `XHDRModelAtP` datum at $p$ for level $\Gamma_M(H)$, with associated curve model $\mathfrak X.\mathrm{Meta}$ over $\overline{\mathbb Q}$ with function field $xHFunctionFieldBar\ M\ H$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit, residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho : R_p \to A$ compatible with $R_p \to \overline{\mathbb Q}$. Further data: a unit $pb$ of $\mathbb Z/(M/p)$ reducing to $p$ and the map $\delta$ on places of $\overline F' = qExpFunctionFieldC\ \kappa\ (\Gamma_N)$ given by the diamond automorphism attached to $pb$; an automorphism $\theta$ of $xHFunctionFieldBar\ M\ H$ over $\overline{\mathbb Q}$ implementing $\mathfrak X.w$ on places of sections; an integral $\overline{\mathbb Q}$-algebra map $\alpha$ from the level-$(M/p)$ field $xHFunctionFieldBar\ (M/p)\ (infSubgroup\ p\ M\ H\ hpM)$ which is the identity on underlying Laurent series, with $\theta \circ \alpha$ also integral; a place specialisation $Psp$ and a prolongation datum $Rpd$ for $Psp$ and $\theta$ whose two residue maps agree along $\alpha$ up to the $p$-power $q$-expansion Frobenius; and the dictionary hypothesis $hcomp$ identifying, for each $i \in \{0,1\}$, the place of a closed point of the fibre model $\mathfrak X.\mathrm{Mfib}$ lying over the reduction of an $A$-section with $Psp.\mathrm{reduceFst}\ \alpha$ (for $i=0$) resp. $Psp.\mathrm{reduceSnd}\ (\theta\circ\alpha)\ \delta$ (for $i=1$) applied to the place of the generic section. Finally fix a place $v$ of $\overline F'$ over $\kappa$ and one $A$-section $yQ$ of $\mathfrak X.\mathrm{Meta}$, with its $A$-point $uQ$ of the integral model, its residue-field section $u\kappa_Q$, and a closed point $P_Q$ of $\mathfrak X.\mathrm{Mfib}$ mapping under $\mathfrak X.\mathrm{efib} \mathrel{\text{followed by}} \mathfrak X.\mathrm{comp}\ 0$ to the closed point of $u\kappa_Q$, such that the place of $P_Q$ is $v$ and the place $W_Q$ of $yQ$ is cuspidal in the sense that every $x$ with $q$-expansion $jqModC$ satisfies $\mathrm{ord}_{W_Q}(x - a) \le 0$ for all $a \in A$. The conclusion asserts the existence of $T$ in the level-$(M/p)$ field, a Laurent series $y$ over $A$ and $g \in qExpFunctionFieldC\ \kappa\ (\Gamma_N)$ with: $y$ maps to the $q$-expansion of $T$ under the inclusion $A \hookrightarrow \overline{\mathbb Q}$ on coefficients; $g$ has $q$-expansion the coefficientwise residue of $y$; $g \ne 0$; $\mathrm{ord}_v(g) = 1$; $\mathrm{ord}_{W_Q}(\alpha T) \ge 1$; and $\mathrm{ord}_{W'}(\alpha T) \ge 0$ for the place $W'$ of every further section $y'$ equipped with the same companion data $u'$, $u\kappa'$, $P'$ over the zeroth component whose place is cuspidal and whose closed point has place $v$.
--
--   This is the section-level form of the statement that a uniformiser at a smooth point $v$ of the mod-$p$ fibre can be lifted to a function defined over the level-$(M/p)$ field which has $A$-integral $q$-expansion, vanishes along the given cuspidal section and is regular along all competing cuspidal sections with the same reduction; it supplies the local coordinate used in the cusp semicontinuity argument on the Deligne–Rapoport model at a prime exactly dividing the level. It is used by [`ModularCurve.XHDRModelAtP.exists_ord_eq_one_section_of_isInftySide_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.exists_ord_eq_one_section_of_isInftySide_prolongationDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_lift_regular_section_comp_zero_ord_placeOfPoint_eq_one_prolongationDatum.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHChartSemicontinuity
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_lift_regular_section_comp_zero_ord_placeOfPoint_eq_one_prolongationDatum
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
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

    (yQ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (uQ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (huQ : barPt A ≫ uQ.1 = yQ.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκQ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκQ₁ : uκQ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ uQ.1)
    (huκQ₂ : uκQ ≫ pullback.snd _ _ = 𝟙 _)
    (PQ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hPQ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base PQ.1 = uκQ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0v : (𝔛.Mfib A hA ρ hρ).placeOfPoint PQ = v)
    (hcQ : (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace yQ)) :
    ∃ (T : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (y : LaurentSeries ↥A)
      (g : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))),
      coeffMap A.subtype y = (T : LaurentSeries (AlgebraicClosure ℚ)) ∧
      ((g : ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y ∧
      g ≠ 0 ∧
      v.ord g = 1 ∧
      1 ≤ (𝔛.Meta.pointEquivPlace yQ).ord (α T) ∧
      ∀ (y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (hu' : barPt A ≫ u'.1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (huκ'₁ : uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u'.1)
        (huκ'₂ : uκ' ≫ pullback.snd _ _ = 𝟙 _)
        (P' : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (hP' : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (𝔛.Meta.pointEquivPlace y') →
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P' = v →
        0 ≤ (𝔛.Meta.pointEquivPlace y').ord (α T) := by sorry
