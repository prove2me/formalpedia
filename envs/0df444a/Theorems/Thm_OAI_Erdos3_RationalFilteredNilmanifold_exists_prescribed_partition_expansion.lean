-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_prescribed_partition_expansion
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_partition_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T07:20:31.130006+00:00
-- url     : https://prove2.me/theorems/c20edb3d-412c-4d65-bd0a-884e0f4c6e92
-- title:
--   The prescribed partition expansion specification holds for suitable exponents B and C
-- statement:
--   For all natural numbers $s, r, b_0$ there is a natural number $B \ge 2$ such that for all natural numbers $k_0, a$ there is a natural number $C \ge 2$ with `PrescribedPartitionExpansionSpec s r b₀ k₀ a B C`. That is a long proposition of OpenAI, not unfolded here. It quantifies over finite families of rational filtered nilmanifolds $D_i$ (degree $s+2$, with adapted bases and square-lattice grids of level $M_i$), $E_j$ and $D_0$ (degree $s+1$), refiltration data $W, R, Q_0$ satisfying `RefilteredProductExpansionSpec` with parameters $p \ge 2$, $q$, $r$ and $0 \le \mathrm{cost} \le (p+b_0)^{b_0}$, under complexity bounds $p$. Its conclusion provides a sublattice version $Q'$ of $Q_0$ with geometry complexity at most $\mathrm{cost}$ such that, for all orbits $g$, $g_0$, shifts $c$, positive $N$ and $0 < \varepsilon \le 1$ with $1/\varepsilon \le \exp((p+2)^a)$, there is a partition of unity $(A_j)_{j \in I}$ on $\mathbb{Z}/N$ with $|I| \le \exp((p+C)^C)$, each $A_j$ a `PositiveCyclicNiltest` of degree $s+2$ and complexity $(p+C)^C$ supported on a set of circle-diameter at most $\varepsilon$, with the property that for suitably invariant niltests $S_h$ of complexity $p$ and a set $H_{\mathrm{sh}}$ of shifts carrying compatible orbit, lattice (coordinate bounds $\exp((p+2)^{k_0})$) and factorization data (slow bounds $\exp((p+2)^r)$), there are unit-interval-valued niltests $U_{i,j,h}$ on $Q'$ of complexity at most $(p+C)^C$ (vanishing when $A_i(x)A_j(x+h) = 0$ for every $x$ outside `cyclicWrapExceptional h ε`) and errors $\mathrm{err}_h$ with $\mathrm{Re}\,S_h(x) = \sum_{i,j} A_i(x)A_j(x+h)\,\mathrm{Re}\,U_{i,j,h}(x) + \mathrm{err}_h(x)$ for $h \in H_{\mathrm{sh}}$ and $\mathbb{E}_x|\mathrm{err}_h(x)| \le \exp((p+B)^B)\,\varepsilon + 3/N$ for every $h$.
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_prescribed_partition_expansion` in `lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B124` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean#L407

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B124

namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u

end Erdos3

namespace Erdos3.RationalFilteredNilmanifold

theorem exists_prescribed_partition_expansion (s r b₀ : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ k₀ a : ℕ, ∃ C : ℕ, 2 ≤ C ∧
      PrescribedPartitionExpansionSpec s r b₀ k₀ a B C := by
  sorry

end Erdos3.RationalFilteredNilmanifold
end OAI
