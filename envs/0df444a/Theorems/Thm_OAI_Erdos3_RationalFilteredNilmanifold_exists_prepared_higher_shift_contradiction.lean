-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_prepared_higher_shift_contradiction
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_prepared_higher_shift_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T07:30:15.652646+00:00
-- url     : https://prove2.me/theorems/ec5573c7-bc8f-410f-abe4-8733bb746c78
-- title:
--   A degree s+1 cyclic shift comparison yields the prepared higher shift contradiction
-- statement:
--   Let $s, r, b_0, k_0, k, c$ be natural numbers with $2 \le c$, and $\varepsilon$ a real number with $0 < \varepsilon < 1$. Assume `CyclicShiftComparison (s+1) (ε/2) c` (at universe $0$). Here `CyclicShiftComparison degree ε' c` is OpenAI's predicate: for every positive natural $N$ and real $p \ge 2$ with $N$ odd and $\exp((p+2)^c) \le N$, and all $f, g, J : \mathbb{Z}/N \to [0, e^{p}]$, if `CyclicNiltestUpperComparison degree N ((p+2)^c) (exp(-(p+2)^c)) f g` holds, then there is a set $E \subseteq \mathbb{Z}/N$ with $|E| \le e^{-p}N$ such that `CyclicNiltestShiftBound (degree-1) N p (exp(-p)) (fun n => f n - (1+ε') g n) J E` holds (for every $h \notin E$ and every unit-interval-valued niltest $T$ of degree at most $\mathrm{degree}-1$ and complexity at most $p$, $\mathbb{E}_x (f(x) - (1+\varepsilon')g(x))J(x+h)\,\mathrm{Re}\,T(x) \le e^{-p}$). Then there is a natural number $D_{\exp} \ge 2$ such that `PreparedHigherShiftContradictionSpec s r b₀ k₀ k Dexp ε` holds. That is a long proposition of OpenAI, not unfolded here: for finite families of rational filtered nilmanifolds $D_i$ (degree $s+2$) and $E_j$, $D_0$ (degree $s+1$), refiltration data $W, R, Q_0$ satisfying `RefilteredProductExpansionSpec` with parameters $p \ge 2$, $q$, $r$ and $0 \le \mathrm{cost} \le (p+b_0)^{b_0}$, complexity bounds $p$, an odd $N \ge \exp((p+2)^{D_{\exp}})$, functions $f_1, f_2, \mathrm{weight} : \mathbb{Z}/N \to [0, e^p]$, $\sigma, \delta \ge \exp(-(p+2)^k)$, invariant niltests $S_h$ and a set $H_{\mathrm{sh}}$ of at least $\sigma N$ shifts $h$ carrying compatible orbit, lattice and factorization data (with coordinate bounds $\exp((p+2)^{k_0})$ and slow bounds $\exp((p+2)^r)$), it is impossible that both `CyclicNiltestUpperComparison (s+2) N ((p+2)^Dexp) (exp(-(p+2)^Dexp)) f₁ f₂` holds and $\delta < \mathbb{E}_n (f_1(n) - (1+\varepsilon)f_2(n))\,\mathrm{weight}(n+h)\,\mathrm{Re}\,S_h(n)$ for every $h \in H_{\mathrm{sh}}$.
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_prepared_higher_shift_contradiction` in `lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B124` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean#L681

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

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

end Erdos3

namespace Erdos3

open scoped BigOperators

universe u v

end Erdos3

section

universe u v

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

universe u v

namespace Erdos3

open scoped TensorProduct BigOperators

end Erdos3

end

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_prepared_higher_shift_contradiction (s r b₀ k₀ k c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ Dexp : ℕ, 2 ≤ Dexp ∧ PreparedHigherShiftContradictionSpec s r b₀ k₀ k Dexp epsilon := by
  sorry

end Erdos3.RationalFilteredNilmanifold
end OAI
