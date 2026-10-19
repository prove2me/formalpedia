-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_prescribed_complement_input_partition_s2
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_complement_input_partition_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:01:56.144646+00:00
-- url     : https://prove2.me/theorems/8445be73-fa3c-4bbd-82fc-765bcc8e5788
-- title:
--   Constants for the prescribed-complement input partition specification
-- statement:
--   For every natural number $s$ there is a natural number $B \ge 2$ such that for all natural numbers $k_0$ and $a$ there is a natural number $C \ge 2$ for which `PrescribedComplementInputPartitionSpec s k₀ a B C` holds.
--
--   `PrescribedComplementInputPartitionSpec s k₀ a B C` is a proposition defined by OpenAI. In outline: for finite families $(D_i)_{i \in \iota}$ of rational filtered nilmanifolds of step $s+1$ (with adapted rational bases and weights, and squared models $V_i$, $Q_i$ built from lattices sandwiched between the scaled integer grid and the denominator grid of a modulus $M_i > 0$), every finite family $(E_j)_{j \in \kappa}$ of rational filtered nilmanifolds of step $s$, every rational filtered nilmanifold $D_0$ of step $s$, and every lattice $\Gamma$ (sandwiched between grids of modulus $m_\Gamma > 0$) on the product nilmanifold built from $D_0$ and the $E_j$, $Q_i$, giving a nilmanifold $W$; and for all one-variable polynomial orbits $g_j$ on $E_j$ and $g_{0,i}$ on $D_i$, integers $c_i$, natural numbers $q, N \ge 1$ and reals $p, \varepsilon$ with $2 \le p$, $\lvert\iota\rvert \le p$, $\lvert\kappa\rvert \le p$, all the $D_i$, $V_i$, $E_j$ and $W$ of geometric complexity at most $p$, the basis coefficients of the adapted bases of rational log-height at most $p$, $q \le e^p$, $0 < \varepsilon \le 1$ and $1/\varepsilon \le e^{(p+2)^a}$: there exist a finite index type $I$ with at most $e^{(p + C)^C}$ elements, functions $A_j : \mathbb{Z}/N\mathbb{Z} \to \mathbb{R}$ ($j \in I$) and labels in $\mathbb{Z}/q\mathbb{Z}$, such that each $A_j$ is a `PositiveCyclicNiltest (s + 1) N ((p + C) ^ C)`, $\sum_j A_j(x) = 1$ for all $x$, every $x$ with $A_j(x) > 0$ reduces modulo $q$ to the label of $j$, any two points in the support of one $A_j$ are within distance $\varepsilon$ on the circle, and, for every shift $h$, branch choice, and real group elements and squared orbits satisfying the stated factorization identities (with the elements $\eta_i$ having coordinates bounded by $e^{(p+2)^{k_0}}$ and $\gamma_i$ in the real lattice), any two points $x, y$ outside the exceptional wrap set `cyclicWrapExceptional h ε` that lie in the supports of $A_j(\cdot)A_b(\cdot + h)$ have orbit points in $W$ at distance at most $e^{(p + B)^B}\varepsilon$.
--
--   The precise content is given by OpenAI's Lean definition; the outline above only indicates its shape.
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_complement_input_partition_s2`, which states OpenAI's `OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_complement_input_partition` (in `lean/OAI/Combinatorics/Progressions/Estimates/PrescribedComplementInputPartition.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B192` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PrescribedComplementInputPartition.lean (declaration OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_complement_input_partition)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B192

section

namespace OAI

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup NilpotentLieFiltration
open scoped TensorProduct

theorem exists_prescribed_complement_input_partition_s2 (s : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ k₀ a : ℕ, ∃ C : ℕ, 2 ≤ C ∧
      PrescribedComplementInputPartitionSpec s k₀ a B C := by
  sorry

end Erdos3.RationalFilteredNilmanifold

end OAI
end
