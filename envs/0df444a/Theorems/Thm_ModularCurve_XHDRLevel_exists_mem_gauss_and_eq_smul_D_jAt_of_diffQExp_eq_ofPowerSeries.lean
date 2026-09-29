-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_mem_gauss_and_eq_smul_D_jAt_of_diffQExp_eq_ofPowerSeries
-- name    : ModularCurve.XHDRLevel.exists_mem_gauss_and_eq_smul_D_jAt_of_diffQExp_eq_ofPowerSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/8af2c234-8ab5-5a2c-ad61-068cb5731680
-- title:
--   Integral q-expansion differentials are g dj with g in W₀
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and write $F =$ [`ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)`](def/ModularCurve_X1.html#L101) for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ of integral $q$-expansions of modular forms of equal weight for the subgroup [`ModularCurve.XHDRLevel.ΓM M H`](def/ModularCurve_XHDRModelAtP.html#L79) of $\mathrm{SL}_2(\mathbb{Z})$. Assume $j(q) = q^{-1}\cdot \mathrm{jNum}(q)$, with $\mathrm{jNum} = E_4^3\,\eta^{-24}\in\mathbb{Z}[[q]]$, lies in the corresponding field for the full group, so that it defines an element `jAt` of $F$. Let $W_0$ be a valuation subring of $F$ assumed to have the following members: $f_0\in W_0$ exactly when there are power series $a,a'$ with coefficients in the subring $\{x\in\mathbb{Q} : (\mathrm{den}\,x, p)=1\}$ of $\mathbb{Q}$, the reduction of $a'$ modulo $p$ being nonzero, with $f_0\cdot a' = a$ in $\mathbb{Q}((q))$. Let $\eta\in\Omega_{F/\mathbb{Q}}$ and $P\in\mathbb{Z}[[q]]$ satisfy $\mathrm{diffQExp}(\eta) = P$, where $\mathrm{diffQExp}$ is the $F$-linear map induced by the derivation $q\,d/dq$ on $\mathbb{Q}((q))$ restricted to $F$. Then there exists $g\in F$ with $g\in W_0$ and $\eta = g\cdot d j$.
--
--   This is the statement that a differential of the modular curve whose $q$-expansion has coefficients in $\mathbb{Z}$ is regular at the Gauss point at $p$: written in the basis $dj$ of $\Omega_{F/\mathbb{Q}}$, its coefficient lies in the valuation ring $W_0$ whose members are the quotients of $p$-integral power series with unit-free denominator nonzero modulo $p$. It feeds the construction of regular extensions of $\omega_f$ across the relevant component of the special fibre, and is used in [`CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField`](thm.html#CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_mem_gauss_and_eq_smul_D_jAt_of_diffQExp_eq_ofPowerSeries.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped MatrixGroups

theorem ModularCurve.XHDRLevel.exists_mem_gauss_and_eq_smul_D_jAt_of_diffQExp_eq_ofPowerSeries (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (W₀ : ValuationSubring ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (hW₀ : (∀ f₀ : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)), f₀ ∈ W₀ ↔
        ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f₀ : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)))
    (η : (@KaehlerDifferential ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))))) (P : PowerSeries ℤ)
    (hΘ : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) η =
      HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ))) :
    ∃ g : ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)), g ∈ W₀ ∧ η = g • @KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H)) _ _ (ModularCurve.instAlgebraIntermediateFieldLaurent (ModularCurve.qExpFunctionFieldC ℚ (ModularCurve.XHDRLevel.ΓM M H))) (ModularCurve.XHDRLevel.jAt (ModularCurve.XHDRLevel.ΓM M H) hj) := by sorry
