-- Prove2me | Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
-- name    : ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/4f8597fc-d977-585e-a706-4f211e8c0427
-- title:
--   Gauss presentations of j(q) and j(qᵖ) over a DVR
-- statement:
--   Let $p$ be a prime, let $L$ be a field of characteristic zero, and let $A$ be a discrete valuation domain equipped with an $A$-algebra structure on $L$ making $L$ the fraction field of $A$; assume $p$, viewed in $A$, lies in the maximal ideal of $A$. Write $\kappa$ for the residue field of $A$. Here [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) is the Laurent series $q^{-1}\cdot(\,$the power series `jNum` $= E_4^3\cdot$`dedekindEtaUnitInv`, with coefficients read in $\mathbb{Q})$, `coeffEmb L` applies $\mathbb{Q}\to L$ to all coefficients, `qExpand ℚ p` is the exponent-scaling ring endomorphism $q\mapsto q^p$ of $\mathbb{Q}((q))$, and `jqModC k` is $q^{-1}$ times the image of `jNum` in $k[[q]]$. The assertion is twofold. First, there exist $x,y\in A[[q]]$ whose reduction $\bar y\in\kappa[[q]]$ is nonzero, such that in $L((q))$ one has $j\cdot y=x$ after mapping $x,y$ into $L[[q]]$, and in $\kappa((q))$ one has $\bar x/\bar y=$ `jqModC` $\kappa$. Second, there exist $x,y\in A[[q]]$ with $\bar y\neq0$ such that $j(q^p)\cdot y=x$ in $L((q))$ and $\bar x/\bar y=(\,$`jqModC` $\kappa)^p$ in $\kappa((q))$.
--
--   This records that the $q$-expansions of $j$ and of $j(q^p)$ admit presentations as quotients of power series integral over $A$, whose reductions modulo the maximal ideal are $\bar j$ and $\bar j^{\,p}$ respectively; the second equality is the Frobenius congruence $j(q^p)\equiv j^p \pmod p$ read in $\kappa((q))$. It is used in the analysis of the valuations of the $q$-expansion function field and of the branches of the modular curves $X_1(Mp)$, $X_1(M)\times X_0(p)$ above $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      ModularCurve.coeffEmb L ModularCurve.jq * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
        = ModularCurve.jqModC (IsLocalRing.ResidueField A)) ∧
    (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
        = ModularCurve.jqModC (IsLocalRing.ResidueField A) ^ p) := by sorry
