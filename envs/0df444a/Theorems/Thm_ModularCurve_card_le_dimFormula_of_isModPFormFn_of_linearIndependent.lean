-- Prove2me | Theorems.Thm_ModularCurve_card_le_dimFormula_of_isModPFormFn_of_linearIndependent
-- name    : ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/c502c235-44b7-5235-a3ca-1bc6319965e9
-- title:
--   Dimension bound for mod p weight-2m modular functions
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $N \ge 1$ be an integer with $p \nmid N$, and let $K$ be an algebraically closed field of characteristic $p$. Let $m \ge 1$ and let $\iota$ be a finite index type. Write $\bar j =$ `jqModC K` $\in K((q))$ for the Laurent series $q^{-1}$ times the reduction to $K$ of the integral power series `jNum`, and let $F =$ `modularFunctionFieldFullC K N` be the intermediate field of $K((q))$ generated over $K$ by the expansions `qExpand K d (jqModC K)` for the nonzero divisors $d$ of $N$. Let $G : \iota \to F$ be a family such that, for each $i$, the Laurent series $G_i$ satisfies `IsModPFormFn K m`, i.e. $G_i^6\,\bar j^{4m}(\bar j - 1728)^{3m}$ is integral over $K[\bar j]$ and $G_i^2\,\bar j^{m}(\bar j - 1728)^{m}$ is integral over $K[\bar j^{-1}]$, and suppose $G$ is linearly independent over $K$. Then, as rational numbers, $$\#\iota \;\le\; (2m-1)\bigl(\mathrm{genusFormula}(N) - 1\bigr) + \lfloor m/2\rfloor\,\nu_2(N) + \lfloor 2m/3\rfloor\,\nu_3(N) + m\,\nu_\infty(N),$$ where $\nu_2(N)$ is the number of $x \in \mathbb{Z}/N$ with $x^2 + 1 = 0$, $\nu_3(N)$ the number with $x^2 + x + 1 = 0$, $\nu_\infty(N) = \sum_{d \mid N}\varphi(\gcd(d, N/d))$ is `cuspCount N`, and $\mathrm{genusFormula}(N) = 1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty(N)/2$ with $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$; the two divisions $\lfloor m/2 \rfloor$ and $\lfloor 2m/3\rfloor$ are natural-number divisions, cast to $\mathbb{Q}$.
--
--   This is the characteristic-$p$ upper bound matching the classical dimension of $M_{2m}(\Gamma_0(N))$: a $K$-linearly independent family of weight-$2m$ mod $p$ modular functions of level $N$, in the integrality formulation of `IsModPFormFn`, has at most that many members. It is obtained by placing all the $G_i$ in the Riemann–Roch space of the explicit weight-$2m$ floor divisor on the curve attached to the full level-$N$ modular function field, and is used in the mod $p$ dimension counts [`ModPForms.exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_of_isAlgClosed`](thm.html#ModPForms.exists_mem_modPMod_ofPowerSeries_eq_qexpOfWeight_of_isModPFormFn_of_isAlgClosed) and [`ModPForms.finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one`](thm.html#ModPForms.finrank_modPMod_two_le_genusFormula_add_cuspCount_sub_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_le_dimFormula_of_isModPFormFn_of_linearIndependent.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K]
    (m : ℕ) (hm : 1 ≤ m) {ι : Type} [Fintype ι]
    (G : ι → ↥(modularFunctionFieldFullC K N)) (hG : ∀ i, IsModPFormFn K m (G i : LaurentSeries K))
    (hli : LinearIndependent K G) :
    (Fintype.card ι : ℚ) ≤ (2 * (m : ℚ) - 1) * (ModularCurve.genusFormula N - 1)
      + ((m / 2 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ) + ((2 * m / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ)
      + (m : ℚ) * (ModularCurve.cuspCount N : ℚ) := by sorry
