-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_ord_eq_one_section_of_isInftySide_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.exists_ord_eq_one_section_of_isInftySide_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/351c2a28-d995-57b7-8233-f7d3c1f620ea
-- title:
--   Uniformiser at one ∞-side cusp over v
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit that becomes $1$ in $(\mathbb Z/(M/p))^\times$, and the hypothesis `hj` that `jqModC ℚ` lies in the $q$-expansion function field of $\mathrm{SL}(2,\mathbb Z)$; let $\mathfrak X$ be a model datum `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ and residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho : R_p \to A$ a ring map compatible with $R_p \to \overline{\mathbb Q}$. Let $pb$ be a unit of $\mathbb Z/(M/p)$ whose value is $p$, and let $\delta$ act on places of $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` as the semilinear automorphism attached to `diamondActionModL` at the $\Gamma_0(M/p)$-lift of $pb$. Let $\theta$ be a $\overline{\mathbb Q}$-algebra automorphism of $F_M =$ `xHFunctionFieldBar M H` which, by `hwgen`, computes the effect on places of the isomorphism `𝔛.w`: whenever two $\overline{\mathbb Q}$-sections $y, y'$ of `𝔛.Meta.toBase` satisfy that $y'$ followed by `𝔛.eeta`, the first pullback projection and `𝔛.w.hom` equals $y$ followed by `𝔛.eeta` and that projection, the place of $y'$ is $\theta$ applied to the place of $y$. Let $\alpha : F_{M/p} \to F_M$ be a $\overline{\mathbb Q}$-algebra map, where $F_{M/p} =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, which is the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral. Let $Psp$ be a place-specialisation datum `JHPlaceSpecialization p M H hpM A`, with reduction maps $r_1(W) = Psp.\mathrm{sp}(W|_\alpha)$ and $r_2(W) = \delta(Psp.\mathrm{sp}(W|_{\theta\circ\alpha}))$, and $Rpd$ a `ProlongationDatum` for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue maps to $\bar F$. Assume `hres₂α`: on elements $\alpha v$ lying in both $R_1$ and $R_2$, the $R_2$-residue is the image of the $R_1$-residue under `qExpFrobeniusModL`; and assume `hcomp`: for each $i \in \{0,1\}$, each $\overline{\mathbb Q}$-section $y$, each lift $u$ over `Spec.map ρ` of $y$ and each $\kappa$-section $u\kappa$ of the fibre compatible with $u$, every closed point $P_0$ of `𝔛.Mfib` mapping under `𝔛.efib` followed by `𝔛.comp … i` to the closed point of $u\kappa$ has place equal to $r_1$ of the place of $y$ when $i = 0$ and to $r_2$ of it when $i = 1$. Finally let $v$ be a place of $\bar F$ over $\kappa$ which is $r_1(c)$ for some place $c$ satisfying `IsInftySide`, and let $Q$ be a place of $F_M$ with `IsInftySide Q` and $r_1(Q) = v$; here `IsInftySide W` means that `IsCuspidal W` holds and that there are $x, x' \in F_M$ with Laurent series `jqModC` and `qExpand p (jqModC)` respectively and some $\tau \in A$ of residue $1$ such that $W$ takes the value $\tau$ at $x'/x^p$. The conclusion is the existence of $s \in F_M$ lying in the valuation subring $R_1$ of $Rpd$ such that $\operatorname{ord}_Q s = 1$, $\operatorname{ord}_W s = 0$ for every $W \ne Q$ with `IsInftySide W` and $r_1(W) = v$, and $\operatorname{ord}_v$ of the $R_1$-residue of $s$ equals $1$.
--
--   This supplies the section needed for the local analysis of the cusps of $X_H(M)$ lying on the $\infty$-side component in the fibre at $p$, when $p$ exactly divides $M$: a function with a simple zero at a prescribed $\infty$-side cusp $Q$, invertible at the remaining $\infty$-side cusps reducing to the same fibre place $v$, and whose first residue is a uniformiser at $v$. It is used by [`ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityInfty_prolongationDatum_of_residue`](thm.html#ModularCurve.XHDRModelAtP.cuspLocalSemicontinuityInfty_prolongationDatum_of_residue), the semicontinuity step for the $\infty$-side cusps in the study of the reduction of $X_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_ord_eq_one_section_of_isInftySide_prolongationDatum.lean

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

theorem ModularCurve.XHDRModelAtP.exists_ord_eq_one_section_of_isInftySide_prolongationDatum
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
    (hv : ∃ c, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceFst α hα) c = v)
    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) Q) (hQv : (Psp.reduceFst α hα) Q = v) :
    ∃ (s : ↥(xHFunctionFieldBar M H)) (hs : s ∈ Rpd.R₁.integers),
      Q.ord s = 1 ∧ (∀ W, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) W → (Psp.reduceFst α hα) W = v → W ≠ Q → W.ord s = 0) ∧ v.ord (Rpd.R₁.residue ⟨s, hs⟩) = 1 := by sorry
