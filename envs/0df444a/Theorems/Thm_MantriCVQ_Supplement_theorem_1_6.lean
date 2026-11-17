-- Prove2me | Theorems.Thm_MantriCVQ_Supplement_theorem_1_6
-- name    : MantriCVQ.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:08:37.337554+00:00
-- url     : https://prove2.me/theorems/247aa9c7-10de-4f55-9a31-ea7dff476cd9
-- title:
--   Theorem 1.6 — an oracle keeping Theorem 1.3 on which every private-coin verifier needs more than $\beta_V h(n)$ messages infinitely often
-- statement:
--   Let $h$ be a height function. There are a classical Boolean oracle $O'_h$ and a total unary language $L'_h$ with the properties of Theorem 1.3 such that the following holds. For every polynomial-time verifier $V$, with private coins allowed, such that $L'_h$ has an interactive proof system relative to $O'_h$ with verifier $V$, completeness at least $2/3$ and soundness error at most $1/3$ against computationally unbounded provers, there is a constant $\beta_V>0$ such that $V$ exchanges more than
--   $$\beta_V\,h(n)$$
--   messages on input $1^n$ for infinitely many $n$.
--
--   Messages are alternating communication slots, empty slots included, and the count on an input is the maximum over all provers and random strings. The theorem shows that the $2h(n)$ messages of the protocol of Theorem 1.3 are optimal up to a constant depending on the verifier, even among private-coin proof systems with unbounded honest provers.
--
--   **Formalization Note** "The properties of Theorem 1.3" is `HeightBounds`. Verifiers are `PrivVerifier`s: private coins, adaptive first speaker, number of slots and message lengths. "More than $\beta_Vh(n)$ messages" is: some coin string and some deterministic prover make the interaction use more than $\beta_Vh(n)$ slots.
--
--   Differences from the source:
--   - generalization: a fixed finite inverse-closed gate set containing H, NOT and Toffoli → the gate set {H, X, Toffoli} for the algorithm and the honest prover; reason: it is contained in every admissible gate set, so the Lean statement implies the paper's for every choice (as in the published goal)
--   - reading: L_h ∉ PH^{O_h}, PH defined with deterministic polynomial-time oracle machines → PH O admits machines that halt within a polynomial clock for this O only; reason: this enlarges PH^O, so L ∉ PH O is the stronger statement (as in the published goal)
--   - generalization: soundness against computationally unbounded provers, classical or quantum, that communicate classically → soundness against every map from input and transcript to a distribution on the next message; reason: every such prover induces these conditional laws, so the class of strategies contains all of them
--   - reading: the honest prover is a uniform polynomial-time quantum algorithm → a memoryless uniform polynomial-size QProver over {H, X, Toffoli}, one circuit per slot, measured; reason: a special case, so its existence is stronger; the paper's prover has this form (as in the published goal)
--   - reading: with 3^{h(n)} queries; makes 4^{h(n)} − 3^{h(n)} queries → exactly 3^{h(n)} oracle gates in the circuit for length n; exactly 4^{h(n)} − 3^{h(n)} oracle gates summed over the prover's slots along every transcript of the schedule; reason: the equality reading of the base mission's Theorems 5.1 and 5.5; it is the stronger reading
--   - encoding: time 3^{h(n)} poly(n) and 4^{h(n)} poly(n) → circuit size and ancilla count at most 3^{h(n)} p(n); verifier decision machine halts within 4^{h(n)} p(n) steps with the oracle O; prover circuit sizes summed at most 4^{h(n)} p(n); one polynomial p; reason: the base mission's convention for time; the oracle-free schedule is polynomial-time by PCVerifier
--   - encoding: 2h(n) messages, h(n) from each party; fewer than n·4^{h(n)}/3 prover bits and n·4^{h(n)} verifier random bits → V.S(1^n) = 2h(n) alternating slots; sums of the lengths of the prover's and of the verifier's slots, compared in ℝ; reason: §3.1 counts every slot as a message; alternation gives h(n) slots to each party; messages have their slot's length
--   - encoding: every polynomial-time verifier V with private coins allowed → every PrivVerifier: oracle machines under a clock polynomial in |w| decide the first speaker, each next message or the decision from (input, coins, transcript), with polynomially many coins and a polynomial slot cap; reason: every polynomial-time private-coin verifier has this form; nothing about the schedule is fixed
--   - encoding: completeness at least 2/3 and soundness error at most 1/3 against computationally unbounded provers → some PStrategy accepts every w ∈ L′ with probability ≥ 2/3, and every PStrategy accepts every w ∉ L′ with probability ≤ 1/3; reason: every prover, classical or quantum, that communicates classically induces such a strategy, and every strategy is played by an unbounded randomized classical prover, so the hypotheses are the paper's
--   - encoding: V exchanges more than β_V h(n) messages on 1^n for infinitely many n; the number of messages is the maximum over provers and random strings → ∀ N, ∃ n ≥ N, ∃ coins r and a deterministic prover with β h(n) < slotsUsed(1^n, r, prover); reason: a maximum exceeds a bound iff some run does; each run of a randomized prover is a run of a deterministic one
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 1.6, p. 5 (PDF p. 7); proof in Appendix B.3, pp. 52–53 (PDF pp. 54–55)

import Mathlib
import Definitions.Def_MantriCVQ_Supplement_HeightFunction
import Definitions.Def_MantriCVQ_Supplement_HeightBounds
import Definitions.Def_MantriCVQ_Supplement_PrivVerifier

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ.Supplement

open MantriCVQ

/-- **Theorem 1.6** (Matching lower bound on the number of messages; Mantri, arXiv:2610.37635 (PDF
sha256 d1fab777…1d0b33), Theorem 1.6, p. 5 (PDF p. 7)): for every height function `h` there are a
classical Boolean oracle `O′_h` and a total unary language `L′_h` with the properties of Theorem 1.3
such that for every polynomial-time verifier `V`, with private coins allowed, for which `L′_h` has an
interactive proof system relative to `O′_h` with verifier `V`, completeness at least `2/3` and
soundness error at most `1/3` against computationally unbounded provers, there is a constant
`β_V > 0` such that `V` exchanges more than `β_V h(n)` messages on input `1^n` for infinitely many `n`.

**Formalization Note** "The properties of Theorem 1.3" is the same predicate `HeightBounds` as in
`theorem_1_3`. A verifier is a `PrivVerifier` (private coins, first speaker, number of slots and
message lengths all adaptive). Completeness is one prover strategy accepting every `w ∈ L′_h` with
probability at least `2/3`; soundness is every strategy accepting every `w ∉ L′_h` with probability
at most `1/3`. "`V` exchanges more than `β_V h(n)` messages on `1^n`" says that the maximum number of
slots (empty slots included) over coin strings and provers exceeds `β_V h(n)`, that is, some coin
string and some deterministic prover make the interaction use more than `β_V h(n)` slots. "Infinitely
many `n`" is `∀ N, ∃ n ≥ N`. -/
theorem theorem_1_6 (h : ℕ → ℕ) (hh : HeightFunction h) :
    ∃ (O : Oracle) (L : Set Str), HeightBounds h O L ∧
      ∀ V : PrivVerifier,
        (∃ σ : PStrategy, ∀ w ∈ L, (2 : ℝ) / 3 ≤ V.acceptProb O σ w) →
        (∀ w : Str, w ∉ L → ∀ σ : PStrategy, V.acceptProb O σ w ≤ 1 / 3) →
        ∃ β : ℝ, 0 < β ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
          ∃ (r : Bits (V.coins.eval (unary n).length)) (prv : List Str → Str),
            β * (h n : ℝ) < (V.slotsUsed O (unary n) (List.ofFn r) prv : ℝ) := by sorry

end MantriCVQ.Supplement
