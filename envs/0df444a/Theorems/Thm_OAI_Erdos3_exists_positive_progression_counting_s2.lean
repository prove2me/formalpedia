-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_positive_progression_counting_s2
-- name    : OAI.Erdos3.exists_positive_progression_counting_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:49.906441+00:00
-- url     : https://prove2.me/theorems/4eb0214a-b962-4ad6-9362-b6cd9474027f
-- title:
--   Pseudorandom weights with distinct-unit slopes count progressions with density close to one
-- statement:
--   Let $s$ be a natural number and $\tau > 0$ a real number. Then there exist a natural number $C \ge 2$ and a real number $\xi_0 > 0$ with the following property.
--
--   Let $N$ be an odd natural number (nonzero) and let $p, \xi$ be reals with $p \ge 2$, $0 < \xi \le \xi_0$ and $e^{(p+2)^C} \le N$. Let $I$ be a type with decidable equality, let `slopes` $: I \to \mathbb{Z}/N$, and let $\mu_i : \mathbb{Z}/N \to \mathbb{R}$ for $i \in I$, such that:
--   - for all $i \ne j$ in $I$, $\texttt{slopes}_i - \texttt{slopes}_j$ is a unit of $\mathbb{Z}/N$;
--   - $0 \le \mu_i(x) \le e^p$ for all $i$ and $x$;
--   - $\bigl| \mathbb{E}_{x \in \mathbb{Z}/N} \mu_i(x) - 1 \bigr| \le 2\xi$ for all $i$;
--   - for every $i$, `CyclicNiltestUpperComparison s N ((p+2)^C) (exp (-(p+2)^C)) (μ i) (fun _ => 1 + ξ)` holds (at universe level $0$). This is OpenAI's predicate: for every Lie algebra $L$ over $\mathbb{Q}$ in universe $0$ (with $\mathbb{R} \otimes_{\mathbb{Q}} L$ a Hausdorff topological vector space over $\mathbb{R}$), every `RationalFilteredNilmanifold L s' dim` $D$ with step $s' \le s$, and every niltest $\mathcal{N}$ on $D$ in one variable of weight $1$ that is $[0,1]$-valued (`UnitIntervalValued`) and has complexity at most $(p+2)^C$ (`ComplexityLE`), one has $\mathbb{E}_{x \in \mathbb{Z}/N} \bigl(\mu_i(x) - (1 + \xi)\bigr) \operatorname{Re} \mathcal{N}(x) \le e^{-(p+2)^C}$, where $\mathcal{N}(x)$ is the cyclic evaluation `evalCyclic N` of the niltest at $x$.
--
--   Then for every finite subset $T \subseteq I$ with $|T| \le s + 2$,
--   $$\Bigl| \mathbb{E}_{x \in \mathbb{Z}/N}\, \mathbb{E}_{d \in \mathbb{Z}/N} \prod_{i \in T} \mu_i(x + \texttt{slopes}_i \cdot d) - 1 \Bigr| \le \tau.$$
--
--   Lean: `OAI.Erdos3.exists_positive_progression_counting_s2`, which states OpenAI's `OAI.Erdos3.exists_positive_progression_counting` (in `lean/OAI/Combinatorics/Progressions/Estimates/MaskedCenteredCounting.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B130` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/MaskedCenteredCounting.lean (declaration OAI.Erdos3.exists_positive_progression_counting)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B130

section

namespace OAI

universe u

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_progression_counting_s2 (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, |(𝔼 x, mu i x) - 1| ≤ 2 * xi) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      ∀ T : Finset I, T.card ≤ s + 2 →
        |(𝔼 x, 𝔼 d, ∏ i ∈ T, mu i (x + slopes i * d)) - 1| ≤ tau := by
  sorry

end Erdos3

end

end OAI
end
