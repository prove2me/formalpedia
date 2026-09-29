-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
-- name    : ModularCurve.XHDRModelAtP.iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/b9d14112-f658-5332-96ee-ef5404df2e10
-- title:
--   Primes over I avoiding v lie in the smooth locus
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$. Assume the Laurent series `jqModC ℚ` (namely $q^{-1}$ times the power-series part of $j$) lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios for $\mathrm{SL}(2,\mathbb{Z})$, and let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj`: a proper flat integral model, locally of finite presentation and with integrally closed affine sections, of the two-chart curve $X$ over $\operatorname{Spec}(R\,p)$ at level $\Gamma_M(M,H)$, together with its auxiliary smooth proper model at level $\Gamma_N$, a geometric curve model over $\overline{\mathbb{Q}}$ identified with the base change, its Galois and $q$-expansion compatibilities, and smoothness and geometric integrality of the generic fibre. Let $v$ be an element of the finite chart algebra `chartAlgFin p (ΓM M H) hj`, a subalgebra of the function field over $R\,p$. Assume the dictionary hypothesis `hdict`: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ in its nonunits, with residue field of characteristic $p$ and algebraically closed, every ring homomorphism $\rho : R\,p \to A$ lifting the structure map to $\overline{\mathbb{Q}}$, every point $y$ of the fibre of the model along the residue map composed with $\rho$, and every prime $\mathfrak{q}$ of the finite chart algebra, if the first projection sends $y$ to the image of $\mathfrak{q}$ under the chart immersion `ιFin` and $v \notin \mathfrak{q}$, then $y$ lies in the range of the component morphism $\mathfrak{X}.\mathrm{comp}\,A\,\rho\,0$ and not in the range of $\mathfrak{X}.\mathrm{comp}\,A\,\rho\,1$. Then for every ideal $I$ of the finite chart algebra whose quotient is module-finite over $R\,p$ and satisfies $I + (v) = (1)$, and every prime $\mathfrak{q} \supseteq I$, the point `ιFin p (ΓM M H) hj` of $\mathfrak{q}$ lies in $\mathfrak{X}.\mathrm{smoothLocus}$.
--
--   This is the step which converts the place-keyed special-fibre dictionary for the integral model of $X_H(M)$ at a prime exactly dividing the level into membership in the smooth locus: primes containing a finite-level ideal $I$ and not containing $v$ sit on one component of the mod-$p$ fibre and off the other, hence away from the crossings. It is used in the construction of one-sided pools of points by base change from level polynomial data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups Polynomial

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.iotaFin_mem_smoothLocus_of_le_of_sup_span_singleton_eq_top
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hdict : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
      (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
      (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)),
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y = (ιFin p (ΓM M H) hj).base 𝔮 →
      v ∉ 𝔮.asIdeal → y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧ y ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)
    (I : Ideal ↥(chartAlgFin p (ΓM M H) hj)) [Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ I)]
    (hIv : I ⊔ Ideal.span {v} = ⊤)
    (𝔮 : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)) (h𝔮 : I ≤ 𝔮.asIdeal) :
    (ιFin p (ΓM M H) hj).base 𝔮 ∈ (𝔛.smoothLocus : Set ↥(X p (ΓM M H) hj)) := by sorry
