-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgFin_of_diffQExp_eq_intSeriesC
-- name    : ModularCurve.XHDRModelAtP.isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgFin_of_diffQExp_eq_intSeriesC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/801c1e15-15e3-5fec-991e-abd0e35dd67a
-- title:
--   Chart-local presentation of η gives regularity after reduction
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbf{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbf{Z}/(M/p))^\times$; assume the $q$-series [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15) lies in the field $F_\top$ generated over $\mathbf{Q}$ by ratios of integral $q$-expansions of modular forms of level $SL(2,\mathbf{Z})$, and let $\mathfrak{X}$ be a model [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81). Write $F =$ `qExpFunctionFieldC ℚ (ΓM M H)` for the corresponding $q$-expansion function field over $\mathbf{Q}$, and $\mathbf{Z}_{(p)} =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of rationals with denominator coprime to $p$. Let $W_0$ be a valuation subring of $F$ characterised by: $f_0 \in W_0$ exactly when there are power series $a, a'$ over $\mathbf{Z}_{(p)}$ with $a'$ having nonzero reduction modulo $p$ (along [`GaloisRep.ratLocalizedAtResidue p`](def/GaloisRep_RatLocalizedAtResidue.html#L15)) and $f_0 \cdot a' = a$ as Laurent series over $\mathbf{Q}$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and let $\rho : \mathbf{Z}_{(p)} \to A$ be a ring map compatible with the inclusion $\mathbf{Z}_{(p)} \hookrightarrow \overline{\mathbf{Q}}$. Let $\eta \in \Omega_{F/\mathbf{Q}}$, let $g \in W_0$ with $\eta = g \cdot \mathrm{d}j$ for $j =$ `jAt (ΓM M H) hj`, and let $P \in \mathbf{Z}[[q]]$ satisfy `diffQExp` $(\eta) = P$ as a Laurent series over $\mathbf{Q}$, where `diffQExp` is the $F$-linear map induced by the derivation $q\,\mathrm{d}/\mathrm{d}q$. Let $\bar x$ be a closed point of the curve $\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho$ over $\kappa$, and let $\mathfrak{p}$ be a prime of the finite chart algebra `chartAlgFin p (ΓM M H) hj` (the elements of $F$ integral over $\mathbf{Z}_{(p)}[j]$) whose image under the base map of `ιFin` equals the image of $\bar x$ under `𝔛.efib` followed by `𝔛.comp A hA ρ hρ 0` followed by `pullback.fst`. Suppose $s$ is a chart element with $s \notin \mathfrak{p}$ and that there are $n, k \in \mathbf{N}$ and chart elements $a_i, b_i$ ($i \in \mathrm{Fin}\,k$) with $s^n \cdot \eta = \sum_i a_i\,\mathrm{d}b_i$ in $\Omega_{F/\mathbf{Q}}$. Then for every $\omega \in \Omega_{F_\kappa/\kappa}$, where $F_\kappa =$ `qExpFunctionFieldC κ (ΓN p M H hpM)`, whose $q$-expansion `diffQExp` $(\omega)$ equals the image `intSeriesC κ P` of $P$ in the Laurent series over $\kappa$, the differential $\omega$ is regular at the place of $F_\kappa$ attached to $\bar x$ by `placeOfPoint`, i.e. $\omega = f \cdot \mathrm{d}\pi$ for some $f$ in that place's valuation subring, $\pi$ a uniformiser.
--
--   This is the per-place regularity step for the reduction of a differential along the component of the Deligne–Rapoport fibre at $p$ met by the cusp $\infty$, in the case of the chart on which $j$ is finite: a presentation of $\eta$ by chart functions near a point $\mathfrak{p}$ forces the $q$-expansion-pinned characteristic-$p$ differential $\omega$ to be regular at the corresponding closed point. It is used in [`CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField`](thm.html#CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField) to obtain regularity at all places outside the prescribed exceptional set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgFin_of_diffQExp_eq_intSeriesC.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_WeierstrassCurve_ReductionMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits

theorem ModularCurve.XHDRModelAtP.isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgFin_of_diffQExp_eq_intSeriesC (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (W₀ : ValuationSubring ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (hW₀ : (∀ f₀ : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)), f₀ ∈ W₀ ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f₀ : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (η : (@KaehlerDifferential ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))))) (g : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (hg : g ∈ W₀)
    (hη : η = g • @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (ModularCurve.XHDRLevel.jAt (ModularCurve.XHDRLevel.ΓM M H) hj))
    (P : PowerSeries ℤ)
    (hΘ : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) η =
      HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ)))
    (xbar : (𝔛.Mfib A hA ρ hρ).C) (hxbar : xbar ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (𝔭 : PrimeSpectrum ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj))
    (h𝔭x : (ModularCurve.XHDRLevel.ιFin p (ModularCurve.XHDRLevel.ΓM M H) hj).base 𝔭 = ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ CategoryTheory.Limits.pullback.fst _ _).base xbar))
    (s : ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj)) (hs : s ∉ 𝔭.asIdeal) (n k : ℕ) (a b : Fin k → ↥(ModularCurve.XHDRLevel.chartAlgFin p (ModularCurve.XHDRLevel.ΓM M H) hj))
    (hreg : ((s : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) ^ n) • η = ∑ i, ((a i : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)))) • @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (b i : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))))
    (ω : Ω[↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM))⁄(IsLocalRing.ResidueField ↥A)])
    (hω : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM)) ω =
      ModularCurve.intSeriesC (IsLocalRing.ResidueField ↥A) P) :
    ((𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨xbar, hxbar⟩).IsRegularAt ω := by sorry
