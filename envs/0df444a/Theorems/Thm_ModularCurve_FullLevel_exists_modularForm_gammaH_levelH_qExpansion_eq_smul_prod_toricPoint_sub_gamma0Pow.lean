-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_sub_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_sub_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/fe878257-e12e-5b7d-b2a7-02a86ba3bde5
-- title:
--   Toric products as modular forms on Γ_H(N²M)
-- statement:
--   Let $N \geq 3$ and $M \geq 1$ be natural numbers, let $p$ be a prime and $k$ a natural number with $p^k \mid M$, let $t$ be a natural number coprime to $N$, and let $c \in \mathbb{Q}$. Write $S = \{ i : 1 \leq i \leq p^k/2,\ p \nmid i \}$ (the integer part of $p^k/2$) and $d = \#S$, and for $u \in \mathbb{C}$ let $X(u)$ denote the first component of [`ModularCurve.toricPoint ℂ N u`](def/ModularCurve_TateSlots.html#L125), that is the Laurent series attached to the power series whose $0$-th coefficient is $u/(1-u)^2$ and whose $m$-th coefficient for $m \geq 1$ is $\sum_{d \mid m,\; N \mid d} (m/d)\,(u^{m/d} + u^{-m/d}) - 2\,[N \mid m]\,\sigma_1(m/N)$. Put $\varepsilon = e^{2\pi i/N}$ and $\zeta = e^{2\pi i/p^k}$. Then there are modular forms $\Phi, \Psi$ of weight $2d$ on the group $\Gamma_H(N^2M) = \{\gamma \in \Gamma_0(N^2M) : \gamma_{22} \equiv 1 \bmod N\}$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$ — here $H$ is the kernel of the reduction $(\mathbb{Z}/N^2M)^\times \to (\mathbb{Z}/N)^\times$ — and a non-zero rational $a$ such that, as Laurent series obtained from the $q$-expansions of width $1$ at $\infty$, $$\widetilde{\Psi} = a\,\bigl(X(\varepsilon^{t}) - X(\varepsilon^{2t})\bigr)^{d}, \qquad \widetilde{\Phi} = a \prod_{i \in S} \Bigl( c\,\bigl(X(\varepsilon^{t}) - X(\varepsilon^{2t})\bigr) - \bigl(X(\zeta^{i}) - X(\varepsilon^{t})\bigr) \Bigr).$$
--
--   The forms $\Phi$ and $\Psi$ realise, as modular forms of weight $2d$ on $\Gamma_H(N^2M)$ with explicit $q$-expansions, the product over the generators of $\mathbb{Z}/p^k$ up to sign of shifted abscissae of toric points on the Tate curve; the factor $\Psi$ supplies the common denominator. It feeds the rationality statement for the coefficients of the kernel polynomial of $\mu_{p^k}$ on the Tate curve, [`ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow`](thm.html#ModularCurve.FullLevel.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_cuspData_xP_mem_range_gamma0Pow), via the division values of weight two provided by [`PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff`](thm.html#PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff) and the level-change identity [`ModularCurve.toricPoint_level_mul`](thm.html#ModularCurve.toricPoint_level_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_sub_gamma0Pow.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.exists_modularForm_gammaH_levelH_qExpansion_eq_smul_prod_toricPoint_sub_gamma0Pow
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (M : ℕ) [NeZero M] (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M)
    (t : ℕ) (ht : t.Coprime N) (c : ℚ) :
    ∃ (Φ Ψ : ModularForm (CohCarrier.GammaH (N ^ 2 * M) (ModularCurve.FullLevel.levelH N M) :
        Subgroup (GL (Fin 2) ℝ)) (2 * (((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card : ℕ) : ℤ))
      (a : ℚ), a ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Ψ) =
        (a : ℂ) • ((ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ t)).1 -
          (ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ (2 * t))).1) ^
            ((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Φ) =
        (a : ℂ) • ∏ i ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i),
          ((c : ℂ) • ((ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ t)).1 -
              (ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ (2 * t))).1) -
            ((ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / ((p ^ k : ℕ) : ℂ)) ^ i)).1 -
              (ModularCurve.toricPoint ℂ N (Complex.exp (2 * Real.pi * Complex.I / N) ^ t)).1)) := by sorry
