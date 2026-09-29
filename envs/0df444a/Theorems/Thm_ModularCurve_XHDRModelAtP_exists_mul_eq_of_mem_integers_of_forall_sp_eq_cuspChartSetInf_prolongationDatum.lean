-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/a1b5880c-9839-59db-a813-4b767e20540f
-- title:
--   Clearing denominators inside the ∞-side cusp chart
-- statement:
--   Let $p$ be a prime and $M>0$ with $p \mid M$, $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^{\times}$ contain every unit becoming $1$ in $(\mathbb{Z}/(M/p))^{\times}$, and assume `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`, with curve model $\mathfrak{X}.\mathrm{Meta}$ of $F_M :=$ `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$; let $A \subset \overline{\mathbb{Q}}$ be a valuation subring in which $p$ is a nonunit, with algebraically closed residue field $\kappa$ of characteristic $p$, and $\rho : R_p \to A$ a ring map composing with $A \hookrightarrow \overline{\mathbb{Q}}$ to the structure map. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ represented by $p$, and $\delta$ the self-map of places of $\bar F :=$ `JHNeronObjectAtP.Fbar p M H hpM κ` given by the semilinear action of the mod-$\ell$ diamond automorphism attached to a $\Gamma_0(M/p)$-lift of $pb$. Let $\theta$ be an $\overline{\mathbb{Q}}$-automorphism of $F_M$ inducing, on $\overline{\mathbb{Q}}$-points of $\mathfrak{X}.\mathrm{Meta}.C$, the action of $\mathfrak{X}.w$ (hypothesis `hwgen`), and $\alpha : F_{M/p} \to F_M$ an integral $\overline{\mathbb{Q}}$-algebra map preserving underlying Laurent series, with $\theta \circ \alpha$ integral as well, where $F_{M/p} :=$ `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`. Let `Psp` be a place-specialisation datum, with specialisation map $\mathrm{sp}$ on places, and `Rpd` a prolongation datum for it relative to $\theta$, with regular prolongations $R_1, R_2$; it is assumed that whenever $\alpha u$ lies in the integers of both $R_1$ and $R_2$, its $R_2$-residue is the $q$-expansion Frobenius `qExpFrobeniusModL` at $p$ of its $R_1$-residue, and that the two components of the fibre curve model $\mathfrak{X}.\mathrm{Mfib}$ read places of $F_M$ by $\mathrm{sp}$ along $\alpha$ for $i=0$ and by $\delta \circ \mathrm{sp}$ along $\theta \circ \alpha$ for $i=1$ (hypothesis `hcomp`, with its point-matching side conditions). Let $v$ be a place of $\bar F$ over $\kappa$ arising as $\mathrm{sp}(c|_{\alpha})$ for some place $c$ of $F_M$ which is `IsInftySide`: cuspidal, and carrying elements with $q$-expansions $j$ and $j(q^p)$ whose ratio $x'/x^p$ has at $c$ a value in $A$ with residue $1$. Let $x' \in F_{M/p}$ have Laurent series `jqModC`, and $t \in F_M$ have Laurent series $j(q^p) \cdot j^{-p}$, and let every element of the cusp chart set $S := \alpha(\text{the elements integral over the pole chart of } x' \text{ over } A) \cup \{\, t - a : a \in A \,\}$ lie in the integers of $R_1$. Finally let $\varphi \in F_{M/p}$ with $\alpha\varphi$ in the integers of $R_1$, regular at every place $u_0$ of $F_{M/p}$ over $\overline{\mathbb{Q}}$ with $\mathrm{sp}(u_0) = v$. Then there are $s, e \in S$ with $\alpha\varphi \cdot e = s$ such that it is not the case that the $R_1$-residue of $e$ lies in the valuation ring of $v$ with residue $0$ there.
--
--   This is the inclusion clause in the construction of a cusp chart at the first reading of an $\infty$-side place: it writes $\alpha\varphi$ as a quotient $s/e$ of two members of the $\infty$-side cusp chart set whose denominator does not reduce to $0$ at $v$. It feeds the construction of the chart itself in [`ModularCurve.XHDRModelAtP.exists_isCuspChartFstAt_of_isInftySide_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.exists_isCuspChartFstAt_of_isInftySide_prolongationDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHCuspChartSet
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_mul_eq_of_mem_integers_of_forall_sp_eq_cuspChartSetInf_prolongationDatum
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
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p)
    (hint : ∀ s ∈ (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t), s ∈ Rpd.R₁.integers)
    (φ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hφ : α φ ∈ Rpd.R₁.integers)
    (hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), Psp.sp u₀ = v → φ ∈ u₀.toValuationSubring) :
    ∃ (s : ↥(xHFunctionFieldBar M H)) (_ : s ∈ (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t))
      (e : ↥(xHFunctionFieldBar M H)) (he : e ∈ (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t)),
      ¬ v.HasValue (Rpd.R₁.residue ⟨e, hint e he⟩) (0 : ResidueField ↥A) ∧ α φ * e = s := by sorry
