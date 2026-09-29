-- Prove2me | Theorems.Thm_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four
-- name    : ModularCurve.six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/846392f5-ef9d-5222-a600-3949d6000a8f
-- title:
--   Manin-symbol bound for elliptic- and parabolic-killing characters of Γ₀(N)
-- statement:
--   Let $N$ be a nonzero natural number, $K$ a field (of arbitrary characteristic), and $\iota$ a finite index type. Let $\varphi$ be a family, indexed by $\iota$, of additive monoid homomorphisms from the additivisation `Additive (CongruenceSubgroup.Gamma0 N)` of the group $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$ to $K$ — equivalently, a family of group homomorphisms $\Gamma_0(N) \to (K,+)$. Assume that this family is linearly independent over $K$ in the $K$-module of all such homomorphisms, and that each member kills all elements of small trace: for every index $i$ and every $\gamma \in \Gamma_0(N)$ whose underlying integral $2 \times 2$ matrix satisfies $(\operatorname{tr}\gamma)^2 \le 4$, one has $\varphi_i(\gamma) = 0$. Then
--   $$6\,\#\iota + 6\,\nu_\infty + 3\,\varepsilon_2 + 4\,\varepsilon_3 \le 12 + [\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)],$$
--   where $\nu_\infty$ is the cardinality of [`ModularCurve.CuspSpace N`](def/ModularCurve_CuspSpace.html#L103), the quotient of $\mathbb{P}^1(\mathbb{Q}) =$ `OnePoint ℚ` by the orbit relation of the image `Gamma0Q N` of $\Gamma_0(N)$ in $\mathrm{GL}_2(\mathbb{Q})$ under `mapGL ℚ`; $\varepsilon_2$ is the number of elements of the coset space $\mathrm{SL}_2(\mathbb{Z})/\Gamma_0(N)$ fixed by $S$; and $\varepsilon_3$ is the number fixed by $ST$, with $S$ and $T$ the standard generators `ModularGroup.S` and `ModularGroup.T`. All cardinalities are the `Nat.card`/`Fintype.card` natural numbers, and the inequality is one of natural numbers.
--
--   This is the Manin-symbol rank bound for $\Gamma_0(N)$: with the classical cusp and elliptic-point counts the inequality reads $\#\iota \le 2g$, $g$ the genus of $X_0(N)$, and it holds over a field of any characteristic, so it bounds the number of independent characters of $\Gamma_0(N)$ vanishing on $\pm 1$ and on all parabolic and elliptic elements. It is used in the construction of additive homomorphisms on $\Gamma_0(N)$ with prescribed exponentials, via [`ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four`](thm.html#ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four.lean

import Mathlib
import Definitions.Def_ModularCurve_CuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four
    (N : ℕ) [NeZero N] (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (φ : ι → (Additive (CongruenceSubgroup.Gamma0 N) →+ K)) (hli : LinearIndependent K φ)
    (hφ : ∀ (i : ι) (γ : CongruenceSubgroup.Gamma0 N),
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → φ i (Additive.ofMul γ) = 0) :
    6 * Fintype.card ι + 6 * Nat.card (ModularCurve.CuspSpace N)
        + 3 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        + 4 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
            (ModularGroup.S * ModularGroup.T) • x = x} ≤
      12 + (CongruenceSubgroup.Gamma0 N).index := by sorry
