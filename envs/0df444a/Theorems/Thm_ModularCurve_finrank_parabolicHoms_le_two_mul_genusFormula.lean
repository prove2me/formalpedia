-- Prove2me | Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_genusFormula
-- name    : ModularCurve.finrank_parabolicHoms_le_two_mul_genusFormula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/9f17692d-cfb8-560d-b46e-cc581ff77365
-- title:
--   dim_K H¹ₚₐᵣ(Γ₀(N),K) ≤ 2g(N)
-- statement:
--   Let $N$ be a nonzero natural number and let $K$ be a field of characteristic zero. Write $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$ for the usual congruence subgroup and let $\mathrm{Period.parabolicHoms}$ denote the $K$-submodule of the additive homomorphisms $\varphi$ from the abelianisation-free additive group $\mathrm{Additive}\,\Gamma_0(N)$ to $K$ consisting of those $\varphi$ satisfying the predicate `IsParabolicHom`, i.e. $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma_0(N)$ whose underlying integral $2\times 2$ matrix has $(\operatorname{tr}\gamma)^2 = 4$ (so $\varphi$ kills $\pm 1$ and all parabolic elements). The assertion is that the $K$-dimension of this space, taken as `Module.finrank` and cast into $\mathbb{Q}$, satisfies $$\dim_K \mathrm{parabolicHoms} \;\le\; 2\left(1 + \frac{\psi(N)}{12} - \frac{\nu_2(N)}{4} - \frac{\nu_3(N)}{3} - \frac{\nu_\infty(N)}{2}\right),$$ where the right-hand side is twice [`ModularCurve.genusFormula N`](def/ModularCurve_GenusNumerics.html#L20), with $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, $\nu_2(N) = \#\{x \in \mathbb{Z}/N : x^2+1 = 0\}$, $\nu_3(N) = \#\{x \in \mathbb{Z}/N : x^2+x+1 = 0\}$ and $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$. Only the inequality is asserted, not the classical equality.
--
--   This is the group-theoretic half of the Eichler–Shimura dimension count: classically the space of parabolic characters of $\Gamma_0(N)$ with values in a characteristic-zero field has dimension exactly $2g(X_0(N))$, and here the upper bound by twice the rational genus formula is recorded. It feeds the comparison of parabolic cohomology with cusp forms and the Eichler–Shimura dimension statement, and thence the Hecke-equivariant period computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_genusFormula.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.finrank_parabolicHoms_le_two_mul_genusFormula (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [CharZero K] :
    (Module.finrank K (ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K) : ℚ) ≤
      2 * ModularCurve.genusFormula N := by sorry
