-- Prove2me | Theorems.Thm_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index
-- name    : ModularCurve.Period.six_mul_finrank_parabolicHoms_add_le_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/278088aa-c9e8-5f31-afbb-900e37712afb
-- title:
--   Signature form of the Eichler–Shimura Betti bound
-- statement:
--   Let $N$ be a positive natural number and let $K$ be a field of characteristic zero. Consider the congruence subgroup $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$ and the following four quantities. First, the $K$-dimension of [`ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K`](def/ModularCurve_PeriodMap.html#L62), the $K$-submodule of the additive homomorphisms $\varphi \colon \mathrm{Additive}\,\Gamma_0(N) \to K$ satisfying $\varphi(\gamma) = 0$ for every $\gamma \in \Gamma_0(N)$ whose underlying integral matrix has trace with square $4$, that is, trace $\pm 2$. Second, the cardinality of [`ModularCurve.CuspSpace N`](def/ModularCurve_CuspSpace.html#L103), the quotient of $\mathbb{P}^1(\mathbb{Q})$ (the one-point compactification `OnePoint ℚ`) by the orbit relation of the image of $\Gamma_0(N)$ in $\mathrm{GL}_2(\mathbb{Q})$ under `mapGL ℚ`. Third, the cardinality of the set of elements of the left coset space $\mathrm{SL}_2(\mathbb{Z})/\Gamma_0(N)$ fixed by the action of $S = \begin{pmatrix}0&-1\\1&0\end{pmatrix}$. Fourth, the cardinality of the set of cosets fixed by $ST = \begin{pmatrix}0&-1\\1&1\end{pmatrix}$. The assertion is the inequality
--   $$6\,\dim_K H + 6\,\nu_\infty + 3\,\varepsilon_2 + 4\,\varepsilon_3 \;\le\; 12 + [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)],$$
--   where the four summands are the quantities just listed in order, and the index is `Subgroup.index`.
--
--   This is the signature form of the upper bound half of the Eichler–Shimura count for $\Gamma_0(N)$: after division by $12$ it says that the space of parabolic characters has dimension at most $2g$, where $g$ is the genus of $\Gamma_0(N)\backslash\mathbb{H}^*$ as computed from the Riemann–Hurwitz signature data (index, elliptic points of order $2$ and $3$, cusps). It is stated purely in terms of the permutation representation of $\mathrm{SL}_2(\mathbb{Z})$ on the cosets of $\Gamma_0(N)$, and is used by [`ModularCurve.finrank_parabolicHoms_le_two_mul_genusFormula`](thm.html#ModularCurve.finrank_parabolicHoms_le_two_mul_genusFormula) to bound the dimension of parabolic homomorphisms by twice the genus formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_CuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.Period.six_mul_finrank_parabolicHoms_add_le_index (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [CharZero K] :
    6 * Module.finrank K (ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K)
        + 6 * Nat.card (ModularCurve.CuspSpace N)
        + 3 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        + 4 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
            (ModularGroup.S * ModularGroup.T) • x = x} ≤
      12 + (CongruenceSubgroup.Gamma0 N).index := by sorry
