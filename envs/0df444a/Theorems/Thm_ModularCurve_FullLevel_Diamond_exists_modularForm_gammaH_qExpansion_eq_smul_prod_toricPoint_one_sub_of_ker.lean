-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_one_sub_of_ker
-- name    : ModularCurve.FullLevel.Diamond.exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_one_sub_of_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/e601b747-2b61-594d-a1f5-e35ce436da56
-- title:
--   Weight 2d forms on Γ_{H^flat}(M') with toric expansions
-- statement:
--   Fix $M'\ge 1$ and $\ell_g$ with $3\le\ell_g$ and $\ell_g\mid M'$, and let $Hb$ be the kernel of the reduction map $(\mathbb Z/M')^{\times}\to(\mathbb Z/\ell_g)^{\times}$; let $p$ be prime, $k$ with $p^{k}\mid M'$, let $t$ be coprime to $\ell_g$ and let $c\in\mathbb Q$. Put $S=\{i: 1\le i\le p^{k}/2,\ p\nmid i\}$ (integer division) and $d=\#S$. The assertion is that there exist modular forms $\Phi,\Psi$ of weight $2d$ for the subgroup of $\mathrm{GL}_2(\mathbb R)$ attached to [`CohCarrier.GammaH M' Hb`](def/CohCarrier_Level.html#L133), namely the image in $\mathrm{SL}_2(\mathbb Z)$ of those $\gamma\in\Gamma_0(M')$ whose lower-right entry reduces into $Hb$ modulo $M'$, together with $a\in\mathbb Q$, $a\ne 0$, such that the $q$-expansions at infinity of period $1$, regarded as Laurent series over $\mathbb C$, satisfy $\widetilde\Psi=a\,(X(\zeta^{t})-X(\zeta^{2t}))^{d}$ and $\widetilde\Phi=a\prod_{i\in S}\bigl(c\,(X(\zeta^{t})-X(\zeta^{2t}))-(X(\zeta_{p^{k}}^{\,i})-X(\zeta^{t}))\bigr)$, where $\zeta=e^{2\pi i/\ell_g}$, $\zeta_{p^{k}}=e^{2\pi i/p^{k}}$, and $X(u)$ is the first component of [`ModularCurve.toricPoint ℂ 1 u`](def/ModularCurve_TateSlots.html#L125): the series with constant term $u/(1-u)^{2}$ and $m$-th coefficient $\sum_{d\mid m} d\,(u^{d}+u^{-d})-2\sigma_1(m)$ for $m\ge 1$.
--
--   This realises the classical division values $12\wp(s/n;\mathbb Z\tau+\mathbb Z)/(2\pi i)^{2}$, and products of their differences, as holomorphic modular forms on the diamond level $\Gamma_{H^\flat}(M')=\Gamma_1(\ell_g)\cap\Gamma_0(M')$, with $q$-expansions matching the abscissae of torsion (toric) points on the Tate curve at level one, i.e. with no stretching of the $q$-parameter. It feeds the computation of [`ModularCurve.FullLevel.Diamond.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_one_fst_mem_range_of_ker`](thm.html#ModularCurve.FullLevel.Diamond.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_one_fst_mem_range_of_ker), where such expansions are compared with coefficients coming from a variable change on the Tate curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_one_sub_of_ker.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.Diamond.exists_modularForm_gammaH_qExpansion_eq_smul_prod_toricPoint_one_sub_of_ker
    (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (Hb : Subgroup (ZMod M')ˣ) (hHb : Hb = (ZMod.unitsMap hℓgM').ker)
    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M')
    (t : ℕ) (ht : t.Coprime ℓg) (c : ℚ) :
    ∃ (Φ Ψ : ModularForm (CohCarrier.GammaH M' Hb :
        Subgroup (GL (Fin 2) ℝ)) (2 * (((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card : ℕ) : ℤ))
      (a : ℚ), a ≠ 0 ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Ψ) =
        (a : ℂ) • ((ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ t)).1 -
          (ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ (2 * t))).1) ^
            ((Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i)).card ∧
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Φ) =
        (a : ℂ) • ∏ i ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun i => ¬ p ∣ i),
          ((c : ℂ) • ((ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ t)).1 -
              (ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ (2 * t))).1) -
            ((ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ((p ^ k : ℕ) : ℂ)) ^ i)).1 -
              (ModularCurve.toricPoint ℂ 1 (Complex.exp (2 * Real.pi * Complex.I / ℓg) ^ t)).1)) := by sorry
