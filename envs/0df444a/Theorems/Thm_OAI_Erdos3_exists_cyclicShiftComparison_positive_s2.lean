-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_cyclicShiftComparison_positive_s2
-- name    : OAI.Erdos3.exists_cyclicShiftComparison_positive_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:48:08.854789+00:00
-- url     : https://prove2.me/theorems/8ca11dc5-1e44-46b7-a022-bc4fa628d978
-- title:
--   For every degree s ≥ 1 and 0 < ε < 1 there is a constant C ≥ 2 for which the cyclic shift comparison holds
-- statement:
--   Let $s$ be a natural number with $1 \le s$ and let $\varepsilon$ be a real number with $0 < \varepsilon < 1$. Then there is a natural number $C \ge 2$ such that `CyclicShiftComparison s ε C` holds (at universe level $0$).
--
--   `CyclicShiftComparison degree ε c` is a proposition defined by OpenAI. It says: for every odd positive integer $N$ and every real $p \ge 2$ with $\exp((p+2)^c) \le N$, and all functions $f, g, J : \mathbb{Z}/N\mathbb{Z} \to \mathbb{R}$ taking values in $[0, e^{p}]$, if
--   - (upper comparison, `CyclicNiltestUpperComparison degree N ((p+2)^c) (exp(-(p+2)^c)) f g`) for every rational filtered nilmanifold (`RationalFilteredNilmanifold`, defined by OpenAI) of filtration length at most $\mathrm{degree}$ and every niltest $T$ on it in one variable that takes values in the unit interval and has complexity at most $(p+2)^c$, one has $\mathbb{E}_{x \in \mathbb{Z}/N}\, (f(x) - g(x)) \operatorname{Re} T_N(x) \le \exp(-(p+2)^c)$, where $T_N(x)$ is the cyclic evaluation `T.evalCyclic N` at $x$,
--
--   then there is a set $E \subseteq \mathbb{Z}/N\mathbb{Z}$ with $|E| \le e^{-p} N$ such that `CyclicNiltestShiftBound (degree - 1) N p (exp(-p)) (f - (1+ε) g) J E` holds: for every $h \notin E$, every rational filtered nilmanifold of filtration length at most $\mathrm{degree} - 1$ (truncated subtraction) and every unit-interval-valued niltest $T$ on it of complexity at most $p$,
--   $$\mathbb{E}_{x \in \mathbb{Z}/N} \bigl(f(x) - (1+\varepsilon) g(x)\bigr)\, J(x + h)\, \operatorname{Re} T_N(x) \le e^{-p}.$$
--
--   Lean: `OAI.Erdos3.exists_cyclicShiftComparison_positive_s2`, which states OpenAI's `OAI.Erdos3.exists_cyclicShiftComparison_positive` (in `lean/OAI/Combinatorics/Progressions/Estimates/AxisCompression.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B130` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AxisCompression.lean (declaration OAI.Erdos3.exists_cyclicShiftComparison_positive)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B130

section

namespace OAI

section

namespace Erdos3

theorem exists_cyclicShiftComparison_positive_s2 (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicShiftComparison.{0} s epsilon C := by
  sorry

end Erdos3

end

end OAI
end
