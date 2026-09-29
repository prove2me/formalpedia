-- Prove2me | Theorems.Thm_ModularCurve_natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne
-- name    : ModularCurve.natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/6904b7a0-6453-5dbe-be1c-5511aec4d600
-- title:
--   p-torsion of J₁(M) in characteristic p counted by Tₚ
-- statement:
--   Let $M \geq 1$ and let $p$ be a prime not dividing $M$, and assume that the space $S_2(\Gamma_1(M)) =$ `CuspForm (CongruenceSubgroup.Gamma1 M) 2` of weight-two cusp forms is finite-dimensional over $\mathbb{C}$. Let $k$ be an algebraically closed field of characteristic $p$, and let $Q \in \mathbb{Z}[X]$ be a polynomial whose image in $\mathbb{C}[X]$ under the canonical map is the characteristic polynomial of the $\mathbb{C}$-linear endomorphism [`CuspForm.heckeTLinOne`](def/CuspForm_Gamma1HeckeOperators.html#L652) of $S_2(\Gamma_1(M))$ at $p$, namely $f \mapsto U_p f + (\langle p \rangle f)|_2 \,\mathrm{diag}$, where $U_p$ is `heckeU`, $\langle p \rangle$ is `diamondLinOne`, and the slash is by `heckeDiagMatrix` at $p$. Then the number of elements $y$ of $J_1(M)(k) :=$ [`ModularCurve.JOneC M k`](def/ModularCurve_X1.html#L209), the group of degree-zero divisors of the $q$-expansion function field [`ModularCurve.x1FunctionFieldC k M`](def/ModularCurve_X1.html#L134) $\subseteq$ `LaurentSeries k` modulo principal divisors, satisfying $p \cdot y = 0$, equals $p^{\,d - e}$, where $d$ is the degree of $Q$ and $e$ is the trailing degree of the reduction of $Q$ modulo $p$, i.e. the multiplicity of $0$ as a root of $\overline{Q} \in \mathbb{F}_p[X]$ (the subtraction being truncated in $\mathbb{N}$).
--
--   This is the Hasse–Witt count for the reduction of $X_1(M)$ at a prime $p \nmid M$: the $p$-rank of the reduced Jacobian equals the number of eigenvalues of $T_p$ on $S_2(\Gamma_1(M))$, with multiplicity, that are units at $p$. It feeds into [`ModularCurve.exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq`](thm.html#ModularCurve.exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq), where the action of $T_p$ on the Tate module of $J_1(M)$ in characteristic $p$ is analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CuspForm_Gamma1HeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    [FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2)]
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]
    (Q : Polynomial ℤ)
    (hQ : Q.map (algebraMap ℤ ℂ) = (CuspForm.heckeTLinOne 2 (Fact.out : p.Prime) hpM).charpoly) :
    Nat.card {y : ModularCurve.JOneC M k // p • y = 0} =
      p ^ (Q.natDegree - (Q.map (Int.castRingHom (ZMod p))).natTrailingDegree) := by sorry
