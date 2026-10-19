-- Prove2me | Theorems.Thm_OAI_Erdos3_PositiveShiftBasis_exists_native_detector_contradiction_s2
-- name    : OAI.Erdos3.PositiveShiftBasis.exists_native_detector_contradiction_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:57:04.258073+00:00
-- url     : https://prove2.me/theorems/1c9d6cab-d57d-403e-9617-66b9efe3a2d4
-- title:
--   A cyclic shift comparison gives a constant for the native detector contradiction
-- statement:
--   Let $s$ and $c$ be natural numbers with $c \ge 2$, and $\varepsilon$ a real number with $0 < \varepsilon < 1$. Assume `CyclicShiftComparison (s+1) (ε/2) c` (at universe level $0$). Then there exists a natural number $C \ge 2$ such that `NativeDetectorContradictionSpec s C ε` holds.
--
--   Here `CyclicShiftComparison degree ε c` is OpenAI's predicate: for every natural number $N \neq 0$ and real $p \ge 2$ with $N$ odd and $e^{(p+2)^c} \le N$, and all $f, g, J : \mathbb Z/N \to [0, e^{p}]$ satisfying `CyclicNiltestUpperComparison degree N ((p+2)^c) (exp(-(p+2)^c)) f g`, there is a set $E \subseteq \mathbb Z/N$ with $|E| \le e^{-p} N$ such that `CyclicNiltestShiftBound (degree - 1) N p (exp(-p)) (fun n => f n - (1+ε) g n) J E` holds. `NativeDetectorContradictionSpec s C ε` is OpenAI's predicate asserting that a list of hypotheses is contradictory: for every `PositiveShiftBasis (s+1) N q (f₁ - (1+ε) f₂) weight` (OpenAI's structure bundling a rational filtered nilmanifold of degree $s+1$ and complexity at most $q$ with a large set of shifts and, for each shift, niltest modes and a unit-interval niltest with prescribed biases) with natural-number weights $w$ on its basis vectors such that each filtration layer $k$ is the $\mathbb Q$-span of the basis vectors of weight at least $k$, and reals $p, p_1, p_2, K, M, \beta_1, \beta_2$ satisfying stated size relations, the existence of two `NativeModelDetector`s (for the shift testing seminorm of the weight and for every native cyclic function), together with $N$ odd, $e^{(p+C)^C} \le N$, $f_1, f_2, \mathrm{weight}$ taking values in $[0, e^{p}]$ and `CyclicNiltestUpperComparison (s+2) N ((p+C)^C) (exp(-(p+C)^C)) f₁ f₂`, implies `False`.
--
--   Lean: `OAI.Erdos3.PositiveShiftBasis.exists_native_detector_contradiction_s2`, which states OpenAI's `OAI.Erdos3.PositiveShiftBasis.exists_native_detector_contradiction` (in `lean/OAI/Combinatorics/Progressions/Estimates/NativeDetectorContradiction.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B230` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/NativeDetectorContradiction.lean (declaration OAI.Erdos3.PositiveShiftBasis.exists_native_detector_contradiction)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B230

section

namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_detector_contradiction_s2 (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeDetectorContradictionSpec s C epsilon := by
  sorry

end Erdos3.PositiveShiftBasis

end

end OAI
end
