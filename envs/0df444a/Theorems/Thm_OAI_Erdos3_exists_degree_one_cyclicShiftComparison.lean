-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_degree_one_cyclicShiftComparison
-- name    : OAI.Erdos3.exists_degree_one_cyclicShiftComparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:26:23.183434+00:00
-- url     : https://prove2.me/theorems/e85268e0-4d95-47ea-b417-6ffcfdf21fec
-- title:
--   The cyclic shift comparison holds in degree one for some exponent
-- statement:
--   Let $\varepsilon$ be a real number with $0 < \varepsilon < 1$. Then there is a natural number $c \ge 2$ such that `CyclicShiftComparison 1 ε c` holds (at universe $0$). Here `CyclicShiftComparison degree ε c` is OpenAI's predicate: for every positive natural $N$ and real $p \ge 2$ with $N$ odd and $\exp((p+2)^c) \le N$, and all $f, g, J : \mathbb{Z}/N \to \mathbb{R}$ with values in $[0, e^{p}]$, if `CyclicNiltestUpperComparison degree N ((p+2)^c) (exp(-(p+2)^c)) f g` holds (for every rational filtered nilmanifold of degree at most `degree` and every unit-interval-valued niltest $T$ of complexity at most $(p+2)^c$ on it, $\mathbb{E}_{x \in \mathbb{Z}/N}\,(f(x) - g(x))\,\mathrm{Re}\,T(x) \le \exp(-(p+2)^c)$), then there is a finite set $E \subseteq \mathbb{Z}/N$ with $|E| \le e^{-p} N$ such that `CyclicNiltestShiftBound (degree-1) N p (exp(-p)) (fun n => f n - (1+ε) g n) J E` holds, that is: for every $h \notin E$, every rational filtered nilmanifold of degree at most $\mathrm{degree} - 1$ (natural subtraction) and every unit-interval-valued niltest $T$ of complexity at most $p$ on it, $\mathbb{E}_{x \in \mathbb{Z}/N}\,(f(x) - (1+\varepsilon)g(x))\,J(x+h)\,\mathrm{Re}\,T(x) \le e^{-p}$.
--
--   Lean: `OAI.Erdos3.exists_degree_one_cyclicShiftComparison` in `lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B107` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/FactoredPositiveShiftContradiction.lean#L443

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B107

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

theorem exists_degree_one_cyclicShiftComparison {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ c : ℕ, 2 ≤ c ∧ CyclicShiftComparison.{0} 1 epsilon c := by
  sorry

end Erdos3
end OAI
