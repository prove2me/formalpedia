-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_kaehlerDifferential_diffQExp_eq_intSeriesC_of_eq_smul_D_jAt_of_mem_gauss
-- name    : ModularCurve.XHDRModelAtP.exists_kaehlerDifferential_diffQExp_eq_intSeriesC_of_eq_smul_D_jAt_of_mem_gauss
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/07c0be36-e055-5ffc-a7cc-2c5fc62c292a
-- title:
--   Mod p reduction of g dj along the Gauss branch
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$; assume the $q$-series $j$, [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15), lies in the $q$-expansion function field of the full level $\mathrm{SL}_2(\mathbb{Z})$, and let $\mathfrak{X}$ be a model datum [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81). Write $F$ for `qExpFunctionFieldC ℚ (XHDRLevel.ΓM M H)`, an intermediate field of $\mathbb{Q}(\!(q)\!)$. Let $W_0 \subseteq F$ be a valuation subring pinned by the stated equivalence: $f_0 \in W_0$ exactly when there are power series $a, a'$ over the subring of rationals with denominator coprime to $p$, with $a'$ having nonzero reduction under `ratLocalizedAtResidue p`, such that $f_0 \cdot a' = a$ in $\mathbb{Q}(\!(q)\!)$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho$ map the $p$-local rationals into $A$ compatibly with $\overline{\mathbb{Q}}$. Given $\eta \in \Omega_{F/\mathbb{Q}}$ of the form $g \cdot dj$ with $g \in W_0$ and $j =$ `XHDRLevel.jAt`, and $P \in \mathbb{Z}[\![q]\!]$ with `diffQExp` $\eta = P$ over $\mathbb{Q}$, the conclusion asserts the existence of $\omega \in \Omega_{F'/\kappa}$, where $F' =$ `qExpFunctionFieldC κ (XHDRLevel.ΓN p M H hpM)`, whose `diffQExp` equals `intSeriesC κ P`, the coefficientwise reduction of $P$ into $\kappa$.
--
--   This is the step of the $q$-expansion principle in which a weight-two differential on the level-$\Gamma_H(M)$ curve, integral along the Gauss (infinity) branch and with integral $q$-expansion, is reduced modulo $p$ to a differential at the lowered level `ΓN` over the residue field, the reduced object being specified only through its $q$-expansion under the operator `diffQExp`. It is used in the proof of [`CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField`](thm.html#CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp_residueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_kaehlerDifferential_diffQExp_eq_intSeriesC_of_eq_smul_D_jAt_of_mem_gauss.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_kaehlerDifferential_diffQExp_eq_intSeriesC_of_eq_smul_D_jAt_of_mem_gauss
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
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
      HahnSeries.ofPowerSeries ℤ ℚ (P.map (Int.castRingHom ℚ))) :
    ∃ ω : Ω[↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM))⁄(IsLocalRing.ResidueField ↥A)],
      ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ModularCurve.XHDRLevel.ΓN p M H hpM)) ω =
        ModularCurve.intSeriesC (IsLocalRing.ResidueField ↥A) P := by sorry
