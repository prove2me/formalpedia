-- Prove2me | Theorems.Thm_MinDilationTree_Sublinear_Supplement_lemma_27
-- name    : MinDilationTree.Sublinear.Supplement.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:01:27.72578+00:00
-- url     : https://prove2.me/theorems/39808c14-9839-42d4-bd23-d81ced075534
-- title:
--   Lemma 27 — a compressed scale sequence in $O(n^2\log n)$ time
-- statement:
--   There is a single deterministic real-RAM algorithm that, given a set $S$ of $n$ distinct points in the plane and $\Lambda\ge6$, computes a compressed scale sequence $(r_0,\ldots,r_N)$ for $S$ and $\Lambda$, consisting of $O(n^2)$ scales, in $O(n^2\log n)$ time. Here a compressed scale sequence satisfies:
--
--   1. for $1\le i\le N$, either $r_i/r_{i-1}=\Lambda$ or $r_i/r_{i-1}\ge\Lambda^{10}$;
--   2. for every pair $p\ne q$ of $S$ there is $i$ with $r_{i-1}\le\|p-q\|<r_i=\Lambda r_{i-1}$;
--   3. $r_0<\|p-q\|$ for every pair $p\ne q$ of $S$.
--
--   The scales are those at which Theorem 29 builds junction trees.
--
--   **Formalization Note** The program and constants $K_0$, $C>0$, $n_0\ge2$ are fixed before the input; for every $n$ the output has length $N+1\le K_0(n^2+1)$, and $t+1\le C\,n^2\log_2 n$ for $n\ge n_0$. $\Lambda$ is part of the input.
--
--   Differences from the source:
--   - reading: an algorithm with running time in O(f(n)), no machine model named → one admissible program of the published exact real RAM (rational literals, no random draws), with ∃ C > 0, ∃ n₀ ≥ 2 fixed with the program before every input (n, points, Λ, r, D and the other inputs), and t + 1 ≤ C·f(n) for n ≥ n₀; correctness for every n; reason: reading R0 of the live mission (the same model as its goal Theorem 1); the paper gives no explicit time constant; its bounds do not depend on Λ, so C is uniform in Λ
--   - encoding: Λ, a parameter assumed ≥ 6 throughout the paper (p. 5, line 171) → Λ an input real with hypothesis 6 ≤ Λ; reason: the paper's standing assumption; Λ is a parameter of the computed sequence
--   - generalization: a compressed scale sequence (the sequence of O(n²) relevant scales of line 627) → a compressed scale sequence of length at most K₀·(n² + 1), K₀ fixed with the program; reason: the paper says the sequence has O(n²) scales and its construction appends at most 10 values per pairwise distance; n² + 1 covers n ≤ 1, where a one-element sequence is required; dropping the clause gives the source's statement
-- source:
--   Sarita de Berg, Jacobus Conradi, Peter Kramer, André Nusser, Sampson Wong, STOC 2027 submission #185 (October 2026), p. 19 (PDF p. 20), Lemma 27 and lines 627–633

import Mathlib
import Definitions.Def_MinDilationTree_Sublinear_Supplement_Encoding

open scoped ENNReal

set_option autoImplicit false

namespace MinDilationTree.Sublinear.Supplement

open MinDilationTree.Sublinear

/-- Lemma 27, p.19 (PDF 20). One admissible real-RAM program computes, for every point set and every
`Λ ≥ 6`, a compressed scale sequence of `O(n²)` scales (length at most `K₀·(n² + 1)`), in
`O(n² log n)` time: `t + 1 ≤ C·n²·log₂ n` for `n ≥ n₀`, with `K₀, C, n₀` fixed with the program. -/
theorem lemma_27 :
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧ ∃ K₀ : ℕ,
      (∀ (n : ℕ) (p : Fin n → Plane), Function.Injective p →
        ∀ Λ : ℝ, 6 ≤ Λ → ∀ ω : MatMulTimeLP.Tape,
          ∃ t : ℕ, MatMulTimeLP.HaltsAt A (enc p ++ [Λ]) ω t ∧
            ∃ R : List ℝ, OutputIs A (enc p ++ [Λ]) ω t (encodeReals R) ∧
              IsCompressedScaleSequence p Λ R ∧ R.length ≤ K₀ * (n ^ 2 + 1)) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
        ∀ (n : ℕ), n₀ ≤ n → ∀ (p : Fin n → Plane), Function.Injective p →
        ∀ Λ : ℝ, 6 ≤ Λ → ∀ ω : MatMulTimeLP.Tape, ∀ t : ℕ,
          MatMulTimeLP.HaltsAt A (enc p ++ [Λ]) ω t →
            (t : ℝ) + 1 ≤ C * (n : ℝ) ^ 2 * log₂ n := by sorry

end MinDilationTree.Sublinear.Supplement
