-- Prove2me | Theorems.Thm_ModularCurve_three_mul_card_orbitRelQuotient_zpowers_S_mul_T_gamma0_eq
-- name    : ModularCurve.three_mul_card_orbitRelQuotient_zpowers_S_mul_T_gamma0_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/05e180ea-783f-558f-9f40-2f569b6b263f
-- title:
--   Order-three elliptic count for Γ₀(N): 3ε₃=ψ(N)+2ν₃(N)
-- statement:
--   Let $N$ be a natural number, assumed nonzero. Consider the left coset space $\mathrm{SL}_2(\mathbb{Z})/\Gamma_0(N)$, where $\Gamma_0(N)$ is Mathlib's congruence subgroup `CongruenceSubgroup.Gamma0 N` of matrices in $\mathrm{SL}_2(\mathbb{Z})$ whose lower-left entry is divisible by $N$, and let the subgroup $\langle ST\rangle$ of integer powers of $ST$, with $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$ and $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ the standard generators, act on this coset space by left translation. The theorem asserts an identity between natural numbers: three times the number of orbits of this action, i.e. the cardinality of the quotient by the orbit relation, equals $\psi(N)+2\nu_3(N)$, where $\psi(N)$ is [`ModularCurve.dedekindPsi N`](def/ModularCurve_X0.html#L201), defined as the sum of $N/d$ over the squarefree divisors $d$ of $N$, and $\nu_3(N)$ is [`ModularCurve.nuThree N`](def/ModularCurve_GenusNumerics.html#L11), defined as the number of $x\in\mathbb{Z}/N\mathbb{Z}$ with $x^2+x+1=0$. No further hypotheses on $N$ are imposed.
--
--   This is the order-three half of the classical count of elliptic points on $X_0(N)$: since $\langle ST\rangle$ has order $6$ with $(ST)^3=-1$, the orbit count is the quantity $\varepsilon_3$ entering the genus formula, and the identity encodes that exactly $\nu_3(N)$ cosets are fixed by $ST$. It is used in the bound [`ModularCurve.finrank_parabolicHoms_gamma0_le_two_mul_genusFormula`](thm.html#ModularCurve.finrank_parabolicHoms_gamma0_le_two_mul_genusFormula), and it is proved from the index computation [`ModularCurve.Gamma0_index`](thm.html#ModularCurve.Gamma0_index) together with the count of $\tau$-stable cyclic subgroups of order $N$ in $(\mathbb{Z}/N\mathbb{Z})^2$ given by [`ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree`](thm.html#ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_three_mul_card_orbitRelQuotient_zpowers_S_mul_T_gamma0_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.three_mul_card_orbitRelQuotient_zpowers_S_mul_T_gamma0_eq (N : ℕ) [NeZero N] :
    3 * Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
        (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N))
      = ModularCurve.dedekindPsi N + 2 * ModularCurve.nuThree N := by sorry
