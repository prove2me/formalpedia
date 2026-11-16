-- Prove2me | Theorems.Thm_FourierSparseTesting1656_Uniform_Supplement_theorem_5_1
-- name    : FourierSparseTesting1656.Uniform.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:14:16.284689+00:00
-- url     : https://prove2.me/theorems/e43d3909-61ff-407e-b918-e857943d2b5e
-- title:
--   Theorem 5.1 — distribution-free Fourier sparsity testing with $O(s\log^3(2s)/\varepsilon)$ queries and $O(1/\varepsilon)$ samples
-- statement:
--   For every $n\ge0$, integer $s\ge1$ and $\varepsilon\in(0,1)$, there is a randomized tester for Boolean functions $f:\mathbb F_2^n\to\{-1,+1\}$ which, given query access to $f$ and sample access to an arbitrary unknown probability distribution $D$ on $\mathbb F_2^n$, makes
--   $$O\!\left(\frac{s\log^3(2s)}{\varepsilon}\right)\text{ queries to }f\quad\text{and}\quad O\!\left(\frac1\varepsilon\right)\text{ samples from }D,$$
--   and satisfies, for every $D$:
--
--   1. it accepts every $f\in F_s$ with probability at least $2/3$;
--   2. it rejects every $f$ with $\operatorname{dist}_D(f,F_s)\ge\varepsilon$ with probability at least $2/3$.
--
--   Here $F_s$ is the class of Boolean functions with at most $s$ nonzero Fourier coefficients (Fourier sparsity in the usual uniform-measure basis; $D$ changes only how distance is measured), $\operatorname{dist}_D(f,g)=\Pr_{x\sim D}[f(x)\ne g(x)]$ and $\operatorname{dist}_D(f,F_s)=\min_{g\in F_s}\operatorname{dist}_D(f,g)$. One tester, fixed from $(n,s,\varepsilon)$, must work for every $D$ and every $f$; it never learns the probabilities of $D$.
--
--   The query complexity matches that of the uniform-distribution tester of Theorem 1.1, so for this class the distribution-free setting costs only the $O(1/\varepsilon)$ samples.
--
--   **Formalization Note** A tester is the supplement's distribution-free model: a finite seed space with a probability law, a fixed sample count $m$, query points computed from the seed and the samples (never from an answer), and an output from the seed, the samples and the ordered answers; the samples are independent draws from $D$, independent of the seed. The constructed tester outputs $1$ (accept) or $0$ (reject); for one absolute constant $C>0$ chosen before $n,s,\varepsilon$ it draws $m\le\lceil C/\varepsilon\rceil$ samples and makes at most $\lceil Cs\log_2^3(2s)/\varepsilon\rceil$ queries on every seed and every sample vector. Acceptance and rejection probabilities are exact finite sums over seeds and sample vectors.
--
--   Differences from the source:
--   - encoding: Boolean f : F₂ⁿ → {−1,+1} → bit function f : (Fin n → ZMod 2) → Bool with false ↦ +1, true ↦ −1; reason: bijective encoding; oracle answers are the bits
--   - encoding: "O(s log³(2s)/ε) queries" and "O(1/ε) samples" → one absolute constant C > 0 quantified before n, s, ε; at most ⌈C·s·log₂(2s)³/ε⌉ queries on every seed and every sample vector, and m ≤ ⌈C/ε⌉ samples; reason: the source's constants are absolute; log(2s) in any fixed base differs from log₂(2s) by a constant factor absorbed into C; the ceilings only round real bounds for natural counts
--   - generalization: "a randomized tester ... given query access to f and sample access to D" → a DistFreeTester: finite seed space with any probability law, m samples drawn up front independently of the seed, query points depending only on the seed and the samples, output from the seed, the samples and the answers; reason: the theorem is existential, so requiring this more restricted form only strengthens it; every such tester is a randomized tester with query and sample access, and Algorithm 4 has this form (finite randomness; p. 23: query locations depend on the samples but on no answer)
--   - encoding: accepts / rejects with probability at least 2/3 → output in {0,1} on every seed, sample vector and answer list, and acceptProb ≥ 2/3, rejectProb ≥ 2/3, exact finite sums over seeds and i.i.d. samples; reason: the probabilities of the run's events under the seed law and the product law of the samples
--   - encoding: distD(f, F_s) = min_{g ∈ F_s} distD(f, g); F_k defined for k ≤ 2ⁿ → distDToSet D f (Fs n s) = infimum of distD D f g over g ∈ Fs n s, with Fs n s defined for every s; reason: F_s is finite and nonempty for s ≥ 1 (proved in the definition file), so the infimum is the minimum; for s ≥ 2ⁿ the class is all Boolean functions, as in the published goal
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), pp. 20–21, Theorem 5.1 (informal version Theorem 1.2, p. 4; model and dist_D p. 20; Algorithm 4 p. 22; proof §5.2, pp. 22–23); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Supplement_DistFree

set_option autoImplicit false
open FourierDimTesting102.Quantum FourierSparseTesting1656.Uniform

namespace FourierSparseTesting1656.Uniform.Supplement

/-- Theorem 5.1, p.20: there is an absolute constant `C > 0` such that for every `n ≥ 0`, integer
`s ≥ 1` and `ε ∈ (0,1)` there is one distribution-free tester `T` (chosen before `D` and `f`) with
outputs in `{0,1}`, at most `⌈C/ε⌉` samples from `D` and at most `⌈C s log₂³(2s)/ε⌉` queries to `f`
on every seed and every sample vector, such that for every distribution `D` on `F₂ⁿ`
1. it accepts every `f ∈ F_s` with probability at least `2/3`;
2. it rejects every `f` with `dist_D(f, F_s) ≥ ε` with probability at least `2/3`. -/
theorem theorem_5_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n s : ℕ) (ε : ℝ), 1 ≤ s → 0 < ε → ε < 1 →
        ∃ T : DistFreeTester n,
          (∀ (σ : T.Seed) (x : Fin T.m → V n) (ans : List Bool),
            T.output σ x ans = 0 ∨ T.output σ x ans = 1) ∧
          T.m ≤ ⌈C / ε⌉₊ ∧
          (∀ (σ : T.Seed) (x : Fin T.m → V n),
            (T.queries σ x).length ≤ ⌈C * s * logTwoS s ^ 3 / ε⌉₊) ∧
          (∀ D : PMF (V n), ∀ f ∈ Fs n s, 2 / 3 ≤ T.acceptProb D f) ∧
          (∀ D : PMF (V n), ∀ f : BoolFn n, ε ≤ distDToSet D f (Fs n s) →
            2 / 3 ≤ T.rejectProb D f) := by sorry

end FourierSparseTesting1656.Uniform.Supplement
