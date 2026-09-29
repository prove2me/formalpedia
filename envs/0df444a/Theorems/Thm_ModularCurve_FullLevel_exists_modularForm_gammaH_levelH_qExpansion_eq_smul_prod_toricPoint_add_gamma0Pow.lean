-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_add_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_add_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/7c592c2a-3684-533c-93d4-7700b13c5b6b
-- title:
--   Weight-2d forms on Γ_H(N²M) with toric q-expansions
-- statement:
--   Let $N\ge 3$ and $M\ge 1$ be nonzero naturals, let $p$ be a prime and $k$ a natural number with $p^k\mid M$, let $t$ be a natural number coprime to $N$, and let $c\in\mathbb Q$. Put $S=\{i\in[1,p^k/2]: p\nmid i\}$ (the natural-division quotient $p^k/2$) and $d=|S|$, and let $\Gamma$ be the image in $\mathrm{GL}_2(\mathbb R)$ of the subgroup of $\mathrm{SL}_2(\mathbb Z)$ consisting of those $\gamma\in\Gamma_0(N^2M)$ whose lower-right entry, as a unit of $\mathbb Z/N^2M$, lies in the kernel of the reduction map $(\mathbb Z/N^2M)^\times\to(\mathbb Z/N)^\times$. Then there exist modular forms $\Phi,\Psi$ of weight $2d$ on $\Gamma$ and a nonzero $a\in\mathbb Q$ such that, writing $X(u)$ for the first component of $\mathrm{toricPoint}_{\mathbb C}(N,u)$ — the Laurent series with constant coefficient $u/(1-u)^2$ and $m$-th coefficient $\sum_{d\mid m,\ N\mid d}(m/d)(u^{m/d}+u^{-m/d})-2[N\mid m]\sigma_1(m/p)$ for $m\ge 1$ — and setting $\varepsilon=e^{2\pi i/N}$, $\zeta=e^{2\pi i/p^k}$, $B_0=X(\varepsilon^t)+\tfrac1{12}$, the $q$-expansions of width $1$ of $\Psi$ and $\Phi$, viewed as Laurent series over $\mathbb C$, are $a\,B_0^{\,d}$ and $a\prod_{i\in S}\bigl(c\,B_0-(X(\zeta^i)-X(\varepsilon^t))\bigr)$ respectively.
--
--   The statement produces, for the given data, weight-$2d$ forms on the level subgroup $\Gamma_H(N^2M)$ whose $q$-expansions are exactly the prescribed products of Tate-curve division values, with $B_0=X(\varepsilon^t)+1/12$ (the single division value $\wp(t/N)$, nonvanishing for every $N\ge 2$, in place of a difference of two division values) serving as the weight-two normaliser. It is used in the study of the coefficients of the variable-change data for the full-level modular curve, in [`ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow_level_fst`](thm.html#ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow_level_fst).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_add_gamma0Pow.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_add_gamma0Pow
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (M : ℕ) [NeZero M] (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M)
    (t : ℕ) (ht : t.Coprime N) (c : ℚ) :
    ∃ (Φ Ψ : ModularForm (CohCarrier.GammaH (N ^ 2 * M) (ModularCurve.FullLevel.levelH N M) :
        Subgroup (GL (Fin 2) ℝ)) (2 * (((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card : ℕ) : ℤ))
      (a : ℚ), a ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Ψ) =
        (a : ℂ) • ((ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ t)).1 +
          HahnSeries.C ((12 : ℂ)⁻¹)) ^
            ((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Φ) =
        (a : ℂ) • ∏ i ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i),
          ((c : ℂ) • ((ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ t)).1 +
              HahnSeries.C ((12 : ℂ)⁻¹)) -
            ((ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / ((p ^ k : ℕ) : ℂ)) ^ i)).1 -
              (ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ t)).1)) := by sorry
