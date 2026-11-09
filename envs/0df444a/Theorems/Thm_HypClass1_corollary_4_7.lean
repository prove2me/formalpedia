-- Prove2me | Theorems.Thm_HypClass1_corollary_4_7
-- name    : HypClass1.corollary_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:34:37.411211+00:00
-- url     : https://prove2.me/theorems/96e006df-0409-43d7-9148-af92c07a45c5
-- title:
--   Corollary 4.7 — $H^{(3)}_{n,p}$ is $(\varepsilon,p,n)$-pseudorandom with probability $\ge 1-n^{-\sqrt C}$
-- statement:
--   Let $C > 0$ be sufficiently large and let $p, \varepsilon \in [0,1]$ satisfy
--   $$
--   p \ge \frac{C\log n}{\varepsilon^4 n}.
--   $$
--   Then with probability at least $1 - n^{-\sqrt C}$ the binomial random 3-graph $H^{(3)}_{n,p}$ is $(\varepsilon, p, n)$-pseudorandom.
--
--   This is where the pseudorandomness used by both stages of the absorption comes from.
--
--   Differences from the source:
--   - reading: 'for sufficiently large C > 0' → ∃ C₀ > 0, ∀ C ≥ C₀, for every n; reason: the standard reading; the statement has no 'n sufficiently large'
--   - encoding: p ≥ C log n/(ε⁴n) for ε ∈ [0,1] → additionally 0 < ε; reason: at ε = 0 the bound C log n/(ε⁴n) is undefined (Lean would read it as 0); this excludes only the undefined case
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Corollary 4.7, p.10

import Mathlib
import Definitions.Def_HypClass1_binomProb
import Definitions.Def_HypClass1_IsPseudorandom3

namespace HypClass1

/-- **Corollary 4.7 (the binomial random 3-graph is pseudorandom).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Corollary 4.7, p.10:
"Let p, ε ∈ [0, 1] be real numbers such that p ≥ C log n/(ε⁴n) for sufficiently large C > 0. Then with
probability at least 1 − n^{−√C} the binomial random 3-graph H^{(3)}_{n,p} is (ε, p, n)-pseudorandom."

**Formalization Note.** `∃ C₀ > 0, ∀ C ≥ C₀`, for every `n` (the statement has no "n large"). `ε > 0` is
assumed: at `ε = 0` the hypothesis `C log n/(ε⁴n)` is undefined (Lean would read it as `0`). The vertex
set is `Fin n` (`W = univ` in `IsPseudorandom3`). -/
theorem corollary_4_7 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ n : ℕ, ∀ p ε : ℝ, 0 ≤ p → p ≤ 1 → 0 < ε → ε ≤ 1 →
      C * Real.log n / (ε ^ 4 * n) ≤ p →
      1 - (n : ℝ) ^ (-Real.sqrt C) ≤ binomProb n p (fun H => IsPseudorandom3 ε p Finset.univ H) := by sorry

end HypClass1
