-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_theorem_1_1
-- name    : IntervalMaxCutEPTAS.Scheme.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:50.098206+00:00
-- url     : https://prove2.me/theorems/05933435-3222-4342-920e-61a30f4fed3c
-- title:
--   Theorem 1.1 — EPTAS for Max-Cut and Max-Bisection on interval graphs
-- statement:
--   There is a deterministic algorithm that, given an interval representation of an unweighted $n$-vertex graph $G$ and a number $\varepsilon\in(0,1)$, computes a set $S\subseteq V(G)$ with
--
--   $$\mathrm{cut}_G(S)\ge(1-\varepsilon)\,\mathrm{mc}(G)$$
--
--   in time $2^{O(\varepsilon^{-2}\log^3(2/\varepsilon))}\cdot n^2$. Within the same time bound it can also compute a set $S$ with $|S|=\lfloor n/2\rfloor$ and $\mathrm{cut}_G(S)\ge(1-\varepsilon)\,\mathrm{mb}(G)$.
--
--   The algorithm is one program uniform in $\varepsilon$; the constant in the exponent is absolute. This is the paper's main result: an efficient polynomial-time approximation scheme for Max-Cut (and Max-Bisection) on interval graphs.
--
--   Differences from the source:
--   - generalization: interval endpoints are real numbers → endpoints in an arbitrary linearly ordered type R; reason: the statement only uses comparisons of endpoints; taking R = ℝ gives the source statement
--   - encoding: time in the word-RAM model with constant-time endpoint comparisons → step count of a program of the published Light language (each primitive operation costs one step, including loads, arithmetic, tests and control flow); reason: explicit charged program syntax with constants quantified before all data; comparing two raw endpoints costs a constant number of steps
--   - encoding: no explicit space bound → space limit S bounded by the same expression; depth limit T; reason: Light runs need finite limits; the source's proof gives this space (PDF p. 19, 21), and a run of T steps cannot nest more than T calls
--   - reading: a number ε ∈ (0, 1) → ε = p/q with naturals 0 < p < q in the input; reason: a program receives a finite description of ε; every rational in (0, 1) is admitted
--   - encoding: 2^{O(ε^{-2} log³(2/ε))}·n² → 2^{C ε^{-2} log₂³(2/ε)}·(n + 1)² with C absolute; reason: for n ≥ 1, (n+1)² ≤ 4n² and the factor 4 is absorbed into the exponent since log₂(2/ε) > 1; the +1 only keeps n = 0 meaningful
--   - reading: words of Θ(log n) bits (§3) → word limit (n + q + 2)^c·⌈2^{c ε^{-2} log₂³(2/ε)}⌉; reason: read Θ(log n) with the finite description of ε fixed; the uniform bound also holds that input and the table addresses used on PDF p. 21, with b computed from ε on PDF p. 22
--   - encoding: “within the same time bound it can also compute” → two programs P₁, P₂ with one constant C; reason: equivalent to one program with a mode bit
--   - encoding: the algorithm outputs a set S → the set is written as a 0/1 array at the returned address and judged on the original representation; reason: a fixed decoding; correctness is for the original input
--   - encoding: the input interval representation, with constant-time endpoint comparisons → an integer representation J with SameComparisons I J, with correctness judged on I; reason: every finite endpoint order, including equalities, has an integer presentation; the universal quantifier over J permits no advice in its magnitudes, and sorting and relabelling cost O(n log n) comparisons within the stated bound
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Theorem 1.1, PDF p. 3 (printed p. 2); restated PDF p. 21, proof PDF p. 22

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Machine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Theorem 1.1: one pair of deterministic programs, with absolute constants, that for every
interval representation of an `n`-vertex graph and every `ε = p/q ∈ (0, 1)` output in time
`2^{O(ε^{-2} log³(2/ε))} · n²` a set `S` with `cut_G(S) ≥ (1 − ε) mc(G)`, respectively a set `S`
with `|S| = ⌊n/2⌋` and `cut_G(S) ≥ (1 − ε) mb(G)`. -/
theorem theorem_1_1 :
    ∃ (P₁ P₂ : Light.Program) (C c : ℕ), ∀ (n p q : ℕ), 0 < p → p < q →
      ∀ {R : Type} [LinearOrder R] (I : Rep R n) (J : Rep ℤ n), SameComparisons I J →
        (∃ T S : ℕ,
            (T : ℝ) ≤ timeF C ((p : ℝ) / q) * ((n : ℝ) + 1) ^ 2 ∧
            (S : ℝ) ≤ timeF C ((p : ℝ) / q) * ((n : ℝ) + 1) ^ 2 ∧
            Light.Ends ⟨(((n + q + 2) ^ c : ℕ) : ℤ) * (⌈timeF c ((p : ℝ) / q)⌉₊ : ℤ), S, T⟩
              P₁ 0 entry (start (encode J p q)) T (ReportsCut I ((p : ℝ) / q) S)) ∧
        (∃ T S : ℕ,
            (T : ℝ) ≤ timeF C ((p : ℝ) / q) * ((n : ℝ) + 1) ^ 2 ∧
            (S : ℝ) ≤ timeF C ((p : ℝ) / q) * ((n : ℝ) + 1) ^ 2 ∧
            Light.Ends ⟨(((n + q + 2) ^ c : ℕ) : ℤ) * (⌈timeF c ((p : ℝ) / q)⌉₊ : ℤ), S, T⟩
              P₂ 0 entry (start (encode J p q)) T (ReportsBis I ((p : ℝ) / q) S)) := by sorry

end IntervalMaxCutEPTAS.Scheme
