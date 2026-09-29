-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgInf_of_diffQExp_eq_intSeriesC
-- name    : ModularCurve.XHDRModelAtP.isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgInf_of_diffQExp_eq_intSeriesC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/f3701a5c-4226-5675-b3e0-fcb09b85cc7a
-- title:
--   Chart-local presentation gives regularity of the reduced differential
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$ but $p^2\nmid M$, and a subgroup $H\le(\mathbf Z/M)^\times$ containing the kernel of the reduction $(\mathbf Z/M)^\times\to(\mathbf Z/(M/p))^\times$; assume $j$, as the Laurent series `jqModC ℚ`, lies in the field $F_{\top}$ generated over $\mathbf Q$ by quotients of $q$-expansions of integral modular forms of full level, and let $\mathfrak X$ be a model datum `XHDRModelAtP p M H hpM hj`. Let $F=$ `qExpFunctionFieldC ℚ (ΓM M H)`. Let $W_0$ be a valuation subring of $F$ whose members are exactly the $f_0$ for which there are power series $a,a'$ over the subring $\mathbf Z_{(p)}\subset\mathbf Q$ of rationals with denominator prime to $p$, the coefficientwise reduction of $a'$ to $\mathbf Z/p$ being nonzero, with $f_0\cdot a'=a$ in the Laurent series over $\mathbf Q$. Let $A$ be a valuation subring of $\overline{\mathbf Q}$ with $p$ a nonunit of $A$, residue field $\kappa$ of characteristic $p$ and algebraically closed, and let $\rho:\mathbf Z_{(p)}\to A$ be a ring map compatible with the inclusion $\mathbf Z_{(p)}\subset\overline{\mathbf Q}$. Let $\eta\in\Omega_{F/\mathbf Q}$ satisfy $\eta=g\,dj$ for some $g\in W_0$, and let $P$ be a power series over $\mathbf Z$ with `diffQExp` of $\eta$ (the $q$-expansion obtained from the derivation $q\,d/dq$) equal to the image of $P$ in the Laurent series over $\mathbf Q$. Let $\bar x$ be a closed point of the curve $\mathfrak X.\mathrm{Mfib}$ attached to $A$, $\rho$, and $\mathfrak p$ a prime of the chart algebra `chartAlgInf p (ΓM M H) hj`, the elements of $F$ integral over $\mathbf Z_{(p)}[j^{-1}]$, whose image under the base map of `ιInf` equals the image of $\bar x$ under the base map of $\mathfrak X.\mathrm{efib}$ followed by $\mathfrak X.\mathrm{comp}\,0$ followed by the first pullback projection. Assume there are $s\notin\mathfrak p$ in that chart algebra, $n,k\in\mathbf N$ and $a,b:\mathrm{Fin}\,k\to$ chart algebra with $s^n\eta=\sum_i a_i\,db_i$ in $\Omega_{F/\mathbf Q}$. Then for every $\omega\in\Omega_{F'/\kappa}$, $F'=$ `qExpFunctionFieldC κ (ΓN p M H hpM)`, whose $q$-expansion `diffQExp` equals the coefficientwise reduction `intSeriesC κ P` of $P$, the place of $F'$ over $\kappa$ attached to $\bar x$ by `placeOfPoint` is regular at $\omega$: there is $f$ in its valuation subring with $\omega=f\cdot d\pi$ for a uniformiser $\pi$ of that place.
--
--   This is the per-place regularity step in the reduction of differentials along the Deligne–Rapoport style integral model at a prime exactly dividing the level: a presentation of $\eta$ by chart functions near $\mathfrak p$ forces the differential on the characteristic-$p$ fibre with the reduced $q$-expansion to be regular at the corresponding place. It is used in [`CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField`](thm.html#CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField) to obtain regularity simultaneously at all places outside a prescribed set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgInf_of_diffQExp_eq_intSeriesC.lean

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

theorem ModularCurve.XHDRModelAtP.isRegularAt_placeOfPoint_of_smul_eq_sum_smul_D_chartAlgInf_of_diffQExp_eq_intSeriesC (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
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
    (𝔭 : PrimeSpectrum ↥(ModularCurve.XHDRLevel.chartAlgInf p (ModularCurve.XHDRLevel.ΓM M H) hj))
    (h𝔭x : (ModularCurve.XHDRLevel.ιInf p (ModularCurve.XHDRLevel.ΓM M H) hj).base 𝔭 = ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ CategoryTheory.Limits.pullback.fst _ _).base xbar))
    (s : ↥(ModularCurve.XHDRLevel.chartAlgInf p (ModularCurve.XHDRLevel.ΓM M H) hj)) (hs : s ∉ 𝔭.asIdeal) (n k : ℕ) (a b : Fin k → ↥(ModularCurve.XHDRLevel.chartAlgInf p (ModularCurve.XHDRLevel.ΓM M H) hj))
    (hreg : ((s : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) ^ n) • η = ∑ i, ((a i : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)))) • @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (b i : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))))
    (ω : Ω[↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM))⁄(IsLocalRing.ResidueField ↥A)])
    (hω : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM)) ω =
      ModularCurve.intSeriesC (IsLocalRing.ResidueField ↥A) P) :
    ((𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨xbar, hxbar⟩).IsRegularAt ω := by sorry
