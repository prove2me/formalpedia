-- Prove2me | Theorems.Thm_FourierSparseTesting1656_Uniform_nonadaptive_fourier_sparsity_tester
-- name    : FourierSparseTesting1656.Uniform.nonadaptive_fourier_sparsity_tester
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:32:18.228201+00:00
-- url     : https://prove2.me/theorems/aaaa3b29-a5a8-4d70-8de9-f84a1917da95
-- title:
--   Theorem 1.1 — a nonadaptive Fourier sparsity tester with $O(s\log^3 s/\varepsilon)$ queries
-- statement:
--   For every $n\ge0$, integer $s\ge1$ and $\varepsilon\in(0,1)$, there is a nonadaptive randomized tester for Boolean functions $f:\mathbb F_2^n\to\{-1,+1\}$ that makes
--   $$O\!\left(\frac{s\log^3(2s)}{\varepsilon}\right)$$
--   oracle queries and satisfies:
--
--   1. it accepts every $f\in F_s$ with probability at least $2/3$;
--   2. it rejects every $f$ with $\operatorname{dist}(f,F_s)\ge\varepsilon$ with probability at least $2/3$.
--
--   Here $F_s$ is the class of Boolean functions with at most $s$ nonzero Fourier coefficients, $\operatorname{dist}$ is the fraction of points of disagreement, and $\operatorname{dist}(f,F_s)$ is the minimum over $F_s$. Nonadaptive means that, for each outcome of the tester's internal randomness, the list of query points is fixed before any answer is seen, and the decision depends only on the randomness and the ordered answers. The query bound holds for every outcome of the randomness.
--
--   This matches the $\Omega(s)$ lower bound up to polylogarithmic factors at constant proximity, and its $1/\varepsilon$ dependence is optimal.
--
--   **Formalization Note** A tester is the referenced nonadaptive query algorithm on the query set $\mathbb F_2^n$: a seed space with a probability measure, a query list for each seed, and an output computed from the seed and the answer list. The constructed tester outputs $1$ (accept) or $0$ (reject), its acceptance event is measurable, and the number of queries is at most $\lceil C s\log_2^3(2s)/\varepsilon\rceil$ on every seed for one absolute constant $C>0$ chosen before $n,s,\varepsilon$.
--
--   Differences from the source:
--
--   - reading: O(s log³ s/ε) with log s (base 2), which is 0 at s = 1 → ⌈C·s·log₂(2s)³/ε⌉; reason: log₂(2s) = 1 + log₂ s is the all-s reading of the asymptotic bound: within a factor 8 of log₂³ s for s ≥ 2, and at s = 1 the literal bound would allow 0 queries although the paper itself states that s = 1 needs Ω(1/ε) queries (p. 3)
--   - encoding: O(·) and "makes O(·) oracle queries" → one absolute constant C > 0 quantified before n, s, ε; the length of the query list is at most the natural ceiling of C·s·log₂(2s)³/ε on every seed; reason: the source's constant is absolute; the ceiling only rounds a real bound for a natural count
--   - encoding: a nonadaptive randomized tester that accepts/rejects → CyclicForrelation.Even.NonadaptiveAlgorithm on queries F₂ⁿ with output in {0,1} (1 = accept, 0 = reject) on every seed and answer list, acceptance event measurable, probabilities under its probability law; reason: queries are fixed by the seed before answers and the decision sees only the seed and the ordered answers, which is nonadaptivity; measurability makes the probabilities those of genuine events
--   - encoding: Boolean f : F₂ⁿ → {−1,+1} → bit function f : (Fin n → ZMod 2) → Bool with false ↦ +1, true ↦ −1; reason: bijective encoding; oracle answers are the bits
--   - encoding: dist(f, F_s) = min over F_s; F_k defined for k ≤ 2ⁿ → distToSet f (Fs n s), with Fs n s defined by the same formula for every s; reason: F_s is finite and contains the constants, so the infimum is the minimum; for s ≥ 2ⁿ the class is all Boolean functions, and the theorem is stated for every integer s ≥ 1
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 3, Theorem 1.1 (definitions §2, pp. 6–7; proof §4, pp. 15–20); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Basic
import Definitions.Def_CyclicForrelation_Even_queryModel

set_option autoImplicit false
open FourierDimTesting102.Quantum CyclicForrelation.Even

namespace FourierSparseTesting1656.Uniform

/-- Theorem 1.1, p.3: there is an absolute constant `C > 0` such that for every `n ≥ 0`, integer
`s ≥ 1` and `ε ∈ (0,1)` there is a nonadaptive randomized tester for Boolean functions on `F₂ⁿ`
(query points fixed by the seed before any answer; decision `1` = accept, `0` = reject, read off
the seed and the ordered answers only) making at most `⌈C s log₂³(2s)/ε⌉` queries on every seed,
which accepts every `f ∈ F_s` with probability at least `2/3` and rejects every `f` with
`dist(f, F_s) ≥ ε` with probability at least `2/3`. -/
theorem nonadaptive_fourier_sparsity_tester :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n s : ℕ) (ε : ℝ), 1 ≤ s → 0 < ε → ε < 1 →
        ∃ A : NonadaptiveAlgorithm (V n),
          (∀ (σ : A.Seed) (ans : List Bool), A.output σ ans = 0 ∨ A.output σ ans = 1) ∧
          CostAtMost A ⌈C * s * logTwoS s ^ 3 / ε⌉₊ ∧
          (∀ f : BoolFn n,
            @MeasurableSet A.Seed A.seedMeasurable {σ | runAlgorithm A f σ = 1}) ∧
          (∀ f ∈ Fs n s, ENNReal.ofReal (2 / 3) ≤ A.law {σ | runAlgorithm A f σ = 1}) ∧
          (∀ f : BoolFn n, ε ≤ distToSet f (Fs n s) →
            ENNReal.ofReal (2 / 3) ≤ A.law {σ | runAlgorithm A f σ = 0}) := by sorry

end FourierSparseTesting1656.Uniform
