-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_initial_relative_absolute_rule_s2
-- name    : OAI.Erdos3.exists_initial_relative_absolute_rule_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:58:44.378033+00:00
-- url     : https://prove2.me/theorems/c55061fc-eb61-485e-a9a3-7bbec024c3dc
-- title:
--   An initial relative patch rule with polynomial cost and a fixed multiplicative gain (1 + ξ)
-- statement:
--   Let $n_0$ be a nonzero natural number and $k \ge 3$ a natural number. Then there exist a natural number $C \ge 2$ and a real number $\xi > 0$ such that for all real numbers $p, a$ with $2 \le p$ and $e^{-p} \le a$, the proposition
--   $$\texttt{RelativePatchAbsoluteRule}\ (k-2)\ n_0\ \bigl((p+2)^{C+1}\bigr)\ a\ \bigl((1+\xi)a\bigr)\ \bigl\lfloor (p+2)^{C} \bigr\rfloor$$
--   holds (the last argument is the natural-number floor). Here `RelativePatchAbsoluteRule s n₀ P a Λ d₀` is a proposition defined by OpenAI; written out for these arguments, with $s = k-2$, $P = (p+2)^{C+1}$, $\Lambda = (1+\xi)a$ and $d_0 = \lfloor (p+2)^C \rfloor$, it says:
--
--   For every $N : \{0, \dots, n_0 - 1\} \to \mathbb{N}$ such that every $N_i$ is prime, the $N_i$ are pairwise distinct, $N_i \le 2^{n_0+1} N_j$ for all $i, j$, and $e^{P} \le N_i$ for all $i$, and for every $f : \mathbb{Z}^{n_0} \to \mathbb{R}$ such that $f(x) \in [0,1]$ for all $x$ in the box $B = \prod_i \{0, 1, \dots, N_i - 1\}$, such that the set $\{x \in B : f(x) \ne 0\}$ contains no $k$-term arithmetic progression $a', a'+d, \dots, a'+(k-1)d$ with $d \in \mathbb{Z}^{n_0}$, $d \ne 0$, and such that $a \le \mathbb{E}_{x \in B} f(x)$, the statement `RelativePatchSliceConclusion (k-2) N f Λ d₀ P` (defined by OpenAI) holds. That statement says: there exist a natural number $q > 0$, a residue slice $S$ of the box with modulus $q$ (an OpenAI `ResidueBoxSlice N q`: starts $b_i$ and lengths $\ell_i$ with $b_i + q j < N_i$ for all $j < \ell_i$), a natural number $d$ and a polynomial patch $A$ (an OpenAI `PolynomialPatch` on the variables $\{0,\dots,n_0-1\}$ with $d$ slots, slot weights between $1$ and $k-2$, and a Lipschitz kernel; its value `A.value t` lies in $[0,1]$ for each $t \in \mathbb{R}^{n_0}$) such that
--   - $e^{-P} N_i \le \ell_i$ for every $i$;
--   - $d \le d_0$;
--   - `relativePatchComplexity A` $\le P$, where `relativePatchComplexity A` $= d + \log(1 + \operatorname{lip})$ with $\operatorname{lip}$ the Lipschitz constant recorded in the kernel of $A$;
--   - $e^{-P} \le$ `relativePatchSliceScore S f Λ A`, where this score is the average over all $x \in \prod_i \{0, \dots, \ell_i - 1\}$ of $\bigl(f(b + q x) - \Lambda\bigr)\cdot$ `A.value x` (with $b + qx$ the point with coordinates $b_i + q x_i$, and $x$ viewed in $\mathbb{R}^{n_0}$ in the second factor).
--
--   Lean: `OAI.Erdos3.exists_initial_relative_absolute_rule_s2`, which states OpenAI's `OAI.Erdos3.exists_initial_relative_absolute_rule` (in `lean/OAI/Combinatorics/Progressions/Estimates/RelativePatchPositivePowerInduction.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B131` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/RelativePatchPositivePowerInduction.lean (declaration OAI.Erdos3.exists_initial_relative_absolute_rule)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B131

section

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_initial_relative_absolute_rule_s2 (n₀ : ℕ) [NeZero n₀]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ {p a : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a →
        RelativePatchAbsoluteRule (k - 2) n₀ ((p + 2) ^ (C + 1)) a ((1 + xi) * a)
          ⌊(p + 2) ^ C⌋₊ := by
  sorry

end Erdos3

end

end OAI
end
