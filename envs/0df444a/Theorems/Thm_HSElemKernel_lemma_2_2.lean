-- Prove2me | Theorems.Thm_HSElemKernel_lemma_2_2
-- name    : HSElemKernel.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:43.005538+00:00
-- url     : https://prove2.me/theorems/7133f91a-3471-44bc-8306-8ce195d0a8be
-- title:
--   Lemma 2.2 — randomized encoding into a $d$-CNF with $O_d(k\log^3 k)$ variables and $O_d(k^d\log^{2d-2} k)$ clauses
-- statement:
--   Fix $d \ge 3$. Given a $d$-Hitting Set instance $(U, \mathcal S, k)$ preprocessed as in Section 2.1, a randomized algorithm constructs a $d$-CNF formula $\Phi$ in expected polynomial time. The formula has $N$ variables and $M$ clauses, where
--   $$N = O_d(k \log^3 k), \qquad M = O_d(k^d \log^{2d-2} k).$$
--   If the input is a NO-instance, then $\Phi$ is unsatisfiable. If the input is a YES-instance, then $\Phi$ is satisfiable with probability at least $3/4$.
--
--   Precisely: for every $d \ge 3$ and every constant $c_0$ there are a program $P$ with fair coins and constants $C > 0$, $K$ such that for every instance of $d$-Hitting Set with $\emptyset \notin \mathcal S$, $\mathcal S \ne \emptyset$, $2 \le k < n$, $n \le c_0k^{d-1}$, $m \le c_0k^d$, and every code $c$ of it:
--
--   1. the expected bit cost on $c$ is at most $C(|c| + 2)^K$, and on every coin sequence on which the run halts, the output is a CNF formula $\Phi$ with clauses of width at most $d$, at most $Ck\log_2^3 k$ variables and at most $Ck^d\log_2^{2d-2} k$ clauses, unsatisfiable if the instance is a NO-instance;
--   2. if the instance is a YES-instance, the event that the run halts with a satisfiable output is measurable and has probability at least $3/4$.
--
--   **Formalization Note** The paper names no machine model. Running times are measured on the published logarithmic-cost RAM with fair coins (`TimeSpaceMA_RAM`, with the cost layer `SoftmaxAttnFD_Machine`): every executed instruction costs one plus the bit lengths of the addresses and values it touches. Inputs are lists of natural numbers placed in memory from cell $0$; outputs are read from memory (cell $0$ holds the output length) through a fixed strict decoder.
--
--   Differences from the source:
--   - reading: "preprocessed as in Section 2.1" → hypotheses ∅ ∉ S, S ≠ ∅, 2 ≤ k < n, n ≤ c₀k^(d−1), m ≤ c₀k^d with the constant c₀ chosen before the program; reason: Section 2.1 applies Lemma 2.1 (n = O_d(k^(d−1)), m = O_d(k^d)) and removes the trivial cases
--   - encoding: polynomial-time algorithm on an unnamed machine → program of the published log-cost RAM TimeSpaceMA_RAM with cost layer SoftmaxAttnFD_Machine; bit cost bounded by C(|c|+2)^K in the input bit length |c|; reason: (expected) polynomial time is the same class on polynomially equivalent machine models
--   - encoding: N = O_d(k log³ k), M = O_d(k^d log^(2d−2) k) → N ≤ C k log₂³ k and M ≤ C k^d log₂^(2d−2) k with C chosen after d and c₀, on every halting coin sequence; reason: k ≥ 2 makes log₂ k ≥ 1, so no shift is needed
--   - encoding: a d-CNF formula Φ with N variables and M clauses → output read by decodeCNF as a published MainResults.CNF N (variables Fin N) whose clauses have length ≤ d; M is the number of clauses; reason: representation of formulas
--   - encoding: NO ⇒ unsatisfiable; YES ⇒ satisfiable with probability ≥ 3/4 → on every halting coin sequence; the coin-tape measure of the measurable event {halts with a satisfiable output}; reason: the expected-cost bound forces halting with probability one
--   - encoding: an instance (U, S, k) as input → U = Fin n, S a Finset of Finsets; input: every code of IsInstCode (any listing order); reason: relabelling a finite universe changes no instance, and every presentation of the instance is covered
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 2.2, p.4

import Mathlib
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_MainResults
import Definitions.Def_HSElemKernel_IsDHS
import Definitions.Def_HSElemKernel_IsYes
import Definitions.Def_HSElemKernel_IsInstCode
import Definitions.Def_HSElemKernel_decodeCNF
import Definitions.Def_HSElemKernel_outputList
import Definitions.Def_HSElemKernel_bitLen

open MeasureTheory
open scoped ENNReal

namespace HSElemKernel

/-- **Lemma 2.2** (randomized encoding; Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 2.2, p.4): given a `d`-Hitting Set
instance `(U, S, k)` preprocessed as in Section 2.1, a randomized algorithm constructs a
`d`-CNF formula `Φ` in expected polynomial time, with `N = O_d(k log³ k)` variables and
`M = O_d(k^d log^{2d−2} k)` clauses. If the input is a NO-instance, `Φ` is unsatisfiable; if it
is a YES-instance, `Φ` is satisfiable with probability at least `3/4`.

For `d ≥ 3` and every constant `c₀` (of Lemma 2.1's bounds) there are a program `P` of the
published log-cost RAM with fair coins and constants `C, K` such that for every `d`-Hitting Set
instance with `∅ ∉ S`, `S ≠ ∅`, `2 ≤ k < n`, `n ≤ c₀k^{d−1}`, `m ≤ c₀k^d` and every code
`c` of it:
1. the expected bit cost is at most `C(|c| + 2)^K`, and on every halting tape the output decodes
   (`decodeCNF`) to a CNF formula `Φ` with clauses of width `≤ d`, `N ≤ C k log₂³ k`
   variables, `M ≤ C k^d log₂^{2d−2} k` clauses, unsatisfiable if the input is a NO-instance;
2. if the input is a YES-instance, the event "the run halts with a satisfiable output" is
   measurable and has probability at least `3/4`.

**Formalization Note** "Preprocessed as in Section 2.1" is the standing assumptions
`∅ ∉ S`, `S ≠ ∅`, `2 ≤ k < |U|` plus the bounds `n = O_d(k^{d−1})`, `m = O_d(k^d)` of
Lemma 2.1, with their constant `c₀` fixed before the program. `k ≥ 2` makes `log₂ k ≥ 1`. -/
theorem lemma_2_2 (d : ℕ) (hd : 3 ≤ d) (c₀ : ℕ) :
    ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ I : HSInstance, IsDHS d I → ∅ ∉ I.S → I.S.Nonempty → 2 ≤ I.k → I.k < I.n →
        I.n ≤ c₀ * I.k ^ (d - 1) → I.S.card ≤ c₀ * I.k ^ d →
        ∀ c : List ℕ, IsInstCode I c →
          SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf c)
            (fun mem => ∃ Φ : Σ N : ℕ, MainResults.CNF N, decodeCNF (outputList mem) = some Φ ∧
              (∀ cl ∈ Φ.2, cl.length ≤ d) ∧
              (Φ.1 : ℝ) ≤ C * I.k * Real.logb 2 I.k ^ 3 ∧
              (Φ.2.length : ℝ) ≤ C * (I.k : ℝ) ^ d * Real.logb 2 I.k ^ (2 * d - 2) ∧
              (¬ IsYes I → ¬ MainResults.Satisfiable Φ.2))
            (C * ((bitLen c : ℝ) + 2) ^ K) ∧
          (IsYes I →
            MeasurableSet {τ : ℕ → Bool | SoftmaxAttnFD.cost P (TimeSpaceMA.memOf c) τ < ⊤ ∧
              ∃ Φ : Σ N : ℕ, MainResults.CNF N, decodeCNF (outputList
                (SoftmaxAttnFD.final P (TimeSpaceMA.memOf c) τ)) = some Φ ∧
                MainResults.Satisfiable Φ.2} ∧
            (3 / 4 : ℝ≥0∞) ≤ SoftmaxAttnFD.coinTape
              {τ : ℕ → Bool | SoftmaxAttnFD.cost P (TimeSpaceMA.memOf c) τ < ⊤ ∧
                ∃ Φ : Σ N : ℕ, MainResults.CNF N, decodeCNF (outputList
                  (SoftmaxAttnFD.final P (TimeSpaceMA.memOf c) τ)) = some Φ ∧
                  MainResults.Satisfiable Φ.2}) := by sorry

end HSElemKernel
