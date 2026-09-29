-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL
-- name    : ModularCurve.XHDRModelAtP.exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/ef05189a-034e-538a-88af-856729d42a51
-- title:
--   Second residue of the cusp coordinate j(qᵖ)j⁻ᵖ
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$ but $p^2\nmid M$, and a subgroup $H\le(\mathbb Z/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb Z/(M/p))^\times$, with $M/p\neq 0$; assume $j$, as the Laurent series `jqModC ℚ`, lies in the full-level $q$-expansion field $\mathrm{qExpFunctionFieldC}\ \mathbb Q\ \top$, and let $\mathfrak X$ be an `XHDRModelAtP` datum for $(p,M,H)$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho: R\,p\to A$ be a ring map compatible with $R\,p\to\overline{\mathbb Q}$. Let $\theta$ be a $\overline{\mathbb Q}$-algebra automorphism of $F_M=\mathrm{xHFunctionFieldBar}\ M\ H$ which is pinned to the involution $\mathfrak X.w$ of the model on $\overline{\mathbb Q}$-points, in the sense that for all $\overline{\mathbb Q}$-points $y,y'$ of $\mathfrak X.\mathrm{Meta}.C$ over the base, if $y'$ followed by $\mathfrak X.\mathrm{eeta}$, the first pullback projection and $\mathfrak X.w.\mathrm{hom}$ equals $y$ followed by $\mathfrak X.\mathrm{eeta}$ and that projection, then the place attached to $y'$ is the image of the place attached to $y$ under the semilinear automorphism $\mathrm{ofAlgAut}\,\theta$. Let $\mathrm{Psp}$ be a `JHPlaceSpecialization` for $(p,M,H,A)$ and $\mathrm{Rpd}$ a prolongation datum for it relative to $\theta$, consisting of two regular prolongations $R_1,R_2$ of $A$ to $F_M$ with residue fields inside $\overline F=\mathrm{qExpFunctionFieldC}\ \kappa\ (\Gamma_N\,p\,M\,H)$, with $f\in R_2$ integral iff $\theta f\in R_1$ integral and $\mathrm{res}_2(f)=\mathrm{res}_1(\theta f)$. Let $\alpha$ be a $\overline{\mathbb Q}$-algebra map from $\mathrm{xHFunctionFieldBar}\ (M/p)\ (\mathrm{infSubgroup}\ p\ M\ H)$ to $F_M$ which is the identity on underlying Laurent series, and assume that on every $\alpha$-image which is integral for both prolongations, $\mathrm{res}_2(\alpha v)=\mathrm{qExpFrobeniusModL}\ \kappa\ (\Gamma_N\,p\,M\,H)\ p\,(\mathrm{res}_1(\alpha v))$, that is, the substitution $q\mapsto q^p$ applied to the first residue. Finally let $x\in F_M$ have $q$-expansion $j$ and $t\in F_M$ have $q$-expansion $\mathrm{qExpand}\ \overline{\mathbb Q}\ p\,(j)\cdot (j^{-1})^p$. The conclusion is that $t$ lies in the valuation subring $R_2.\mathrm{integers}$ and that its second residue, read as a Laurent series over $\kappa$, equals $\bar j\cdot(\mathrm{qExpand}\ \kappa\ p\,(\bar j))^{-p}$, with the roles of $\bar j$ and $\bar j(q^p)$ interchanged relative to the $q$-expansion of $t$.
--
--   This is the computation of the cusp coordinate on the $\infty$-side chart of the Deligne–Rapoport model of $X_H(M)$ at $p$, in the Atkin–Lehner branch fixed by $\theta$: the function $t=j(q^p)j^{-p}$ is integral for the second prolongation and reduces to $\bar j\,\bar j(q^p)^{-p}$. It is used by [`ModularCurve.XHDRModelAtP.chartEtaleAt_cuspChartSetInf_of_isInftySide_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.chartEtaleAt_cuspChartSetInf_of_isInftySide_prolongationDatum) to verify that the chart is étale at the cusps on the $\infty$-side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))

    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p) :
    ∃ h₂ : t ∈ Rpd.R₂.integers,
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((Rpd.R₂.residue ⟨t, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) =
        jqModC (ResidueField ↥A) * ((qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)))⁻¹) ^ p := by sorry
