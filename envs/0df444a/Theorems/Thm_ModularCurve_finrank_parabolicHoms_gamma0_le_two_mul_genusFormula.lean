-- Prove2me | Theorems.Thm_ModularCurve_finrank_parabolicHoms_gamma0_le_two_mul_genusFormula
-- name    : ModularCurve.finrank_parabolicHoms_gamma0_le_two_mul_genusFormula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/b027296b-dc6d-56dc-a45a-adcbb745f23f
-- title:
--   Parabolic homomorphisms of Γ₀(N): bound by 2g
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $K$ be a field (in the lowest universe) of characteristic zero. Consider the $K$-submodule [`ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K`](def/ModularCurve_PeriodMap.html#L62) of the space of additive homomorphisms $\mathrm{Additive}(\Gamma_0(N)) \to K$, namely those $\varphi$ with $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma_0(N)$ whose underlying integer matrix satisfies $\mathrm{tr}(\gamma)^2 = 4$, i.e. $\mathrm{tr}(\gamma) = \pm 2$. The assertion is that the $K$-dimension of this submodule, viewed as a rational number, satisfies $$\dim_K \le 2\Bigl(1 + \tfrac{\psi(N)}{12} - \tfrac{\nu_2(N)}{4} - \tfrac{\nu_3(N)}{3} - \tfrac{\nu_\infty(N)}{2}\Bigr),$$ where the right-hand side is twice [`ModularCurve.genusFormula N`](def/ModularCurve_GenusNumerics.html#L20), computed in $\mathbb{Q}$ from: $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$ (`dedekindPsi`), $\nu_2(N) = \#\{x \in \mathbb{Z}/N : x^2 + 1 = 0\}$ (`nuTwo`), $\nu_3(N) = \#\{x \in \mathbb{Z}/N : x^2 + x + 1 = 0\}$ (`nuThree`), and $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$ (`cuspCount`). No hypothesis excluding elliptic points is imposed, and no integrality of the right-hand side is asserted.
--
--   This is the elementary half of the Eichler–Shimura comparison at level $\Gamma_0(N)$: the parabolic cohomology of $\Gamma_0(N)$ with trivial $K$-coefficients, presented concretely as the space of homomorphisms killing all elements of trace $\pm 2$, has dimension at most twice the genus of $X_0(N)$ as given by the classical genus formula. It feeds the bound [`CuspForm.finrank_gamma0_weight_two_le_genusFormula`](thm.html#CuspForm.finrank_gamma0_weight_two_le_genusFormula) on the dimension of the space of weight-two cusp forms for $\Gamma_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_parabolicHoms_gamma0_le_two_mul_genusFormula.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finrank_parabolicHoms_gamma0_le_two_mul_genusFormula (N : ℕ) [NeZero N] (K : Type) [Field K] [CharZero K] :
    (Module.finrank K (ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K) : ℚ)
      ≤ 2 * ModularCurve.genusFormula N := by sorry
