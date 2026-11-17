-- Prove2me | Theorems.Thm_MantriCVQ_Supplement_theorem_B_4
-- name    : MantriCVQ.Supplement.theorem_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:12:51.521295+00:00
-- url     : https://prove2.me/theorems/98f7b5cd-8986-4ccd-aa2b-8efbeaa52406
-- title:
--   Theorem B.4 — a public-coin verifier running in time $n^a$ that is correct at height $h\ge42a$ uses at least $h/(14a)$ slots
-- statement:
--   Fix the degree $d$ of the code family. For every $a\ge1$ there is a threshold on $n$, depending only on $a$ and $d$, beyond which the following holds for every $h\le h_{\max}(n)$ with $h\ge42a$. Every public-coin verifier that runs in time at most $n^a$ on input $1^n$ with every oracle, prover and random string, and whose protocol is correct on every valid instance of size $n$ and height $h$, uses at least
--   $$\frac{h}{14a}$$
--   communication slots.
--
--   Here the instance is the leaf table stored at the addresses $1^n0w$, every other oracle answer is fixed, and the protocol is correct on an instance if its value (the maximum acceptance probability over provers) is at least $2/3$ when the root value is one and at most $1/3$ when it is zero. Combined with the Goldwasser–Sipser transformation and a diagonalization, this gives the message lower bound of Theorem 1.6.
--
--   **Formalization Note** The verifier is a fixed-schedule public-coin `PCVerifier`; its slot count on $1^n$ is $V.S(1^n)$, empty slots included. The time bound is imposed on the decision only, for every oracle and every transcript of the schedule; alternatively, the hypothesis accepts a verifier whose prover slots have length at most $2n^a$ and whose decision makes at most $n^a$ oracle queries, which is the fixed-length form the paper gives (App. B.2, p. 51) to a verifier whose replies may have any length. The other oracle answers are an arbitrary fixed oracle $O_0$.
--
--   Differences from the source:
--   - generalization: the verifier runs in time at most n^a on input 1^n with every oracle, prover and random string → for every oracle and every transcript of the schedule, the clocked run of the decision machine is over within ⌊n^a⌋ steps (D halts by then, or its clock is ≤ ⌊n^a⌋); the schedule is not constrained; reason: every verifier of the paper satisfies this; the proof uses only the bound on the decision's steps (q ≤ n^a queries, replies read to n^a bits)
--   - generalization: a public-coin verifier whose prover replies may have any length (App. B.2, p. 51: "We encode each genuine prover reply by its length followed by padding to ⌊n^a⌋ bits") → a PCVerifier (prover replies of lengths fixed by the input), with the time hypothesis replaced, as an alternative, by: every prover slot has length ≤ 2n^a and the decision makes ≤ ⌊n^a⌋ oracle queries along every transcript of the schedule, with no bound on its steps; reason: the paper's own padding (p. 51) turns every verifier of the theorem into such a PCVerifier with the same slots and the same value on every instance (at most 2n^a bits per reply, q ≤ n^a); the proof uses only q ≤ n^a and S ≤ 2rn^a
--   - encoding: a protocol correct on every valid instance of size n and height h, every other oracle answer fixed; the value is the maximum over provers → for a fixed but arbitrary O₀ and every exactly valid leaf table Y: root 1 → some Strategy is accepted with probability ≥ 2/3 on leafOracle O₀ n h Y; root 0 → every Strategy ≤ 1/3; reason: the maximum of a finite public-coin game is attained, so value ≥ 2/3 iff some strategy reaches 2/3
--   - encoding: a ≥ 1; a threshold depending only on a and d; uses at least h/(14a) slots → a real, ∃ n₀ before ∀ C : CodeDeg d; (h : ℝ)/(14a) ≤ V.S(1^n); reason: Appendix B uses the code family only through its degree; the number of slots of a fixed-schedule verifier is its slot count
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem B.4, p. 51 (PDF p. 53); setting of Appendix B.2, p. 49 (PDF p. 51)

import Mathlib
import Definitions.Def_MantriCVQ_Supplement_leafOracle
import Definitions.Def_MantriCVQ_CodeDeg
import Definitions.Def_MantriCVQ_nodeVal
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_MantriCVQ_Implements53
import Definitions.Def_MantriCVQ_acceptProb
import Definitions.Def_MantriCVQ_queryCount

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ.Supplement

open MantriCVQ

/-- **Theorem B.4** (Message lower bound at a fixed size and height; Mantri, arXiv:2610.37635 (PDF
sha256 d1fab777…1d0b33), Theorem B.4, p. 51 (PDF p. 53); setting of App. B.2, p. 49 (PDF p. 51)): for
every `a ≥ 1` there is a threshold on `n`, depending only on `a` and `d`, beyond which the following
holds for every `h ≤ h_max(n)` with `h ≥ 42a`. Every public-coin verifier that runs in time at most
`n^a` on input `1^n` with every oracle, prover and random string, and whose protocol is correct on every
valid instance of size `n` and height `h`, uses at least `h/(14a)` communication slots.

**Formalization Note** `a` is real and the threshold `n₀` is chosen before the code family, which
enters only through its degree `d`. The verifier is a `PCVerifier` (fixed schedule, public coins) on
input `1^n`. "Runs in time at most `n^a`" is required of the decision only: for every oracle and every
transcript of the schedule, the clocked run of `D` that makes the decision is over within `⌊n^a⌋`
steps (`D` halts by then, or its clock is at most `⌊n^a⌋`); the schedule is not constrained. A
`PCVerifier` receives prover replies of lengths fixed by the input, whereas the paper's verifier may
receive replies of any length; the paper puts such a verifier into fixed-length form by encoding each
reply by its length followed by padding, using at most `2n^a` bits per reply, with the same slots, the
same value on every instance and at most `n^a` queries (App. B.2, p. 51 (PDF p. 53)). The hypothesis
therefore also admits, as an alternative, a verifier whose prover slots have length at most `2n^a`
and whose decision makes at most `⌊n^a⌋` oracle queries along every transcript of the schedule, with
no bound on its steps; this covers every verifier of the paper. The instance is the leaf table `Y` stored at the addresses
`1^n 0 w` with every other answer given by a fixed but arbitrary `O₀` (`leafOracle`). Correct on `Y`:
when the root value is `1` some prover strategy is accepted with probability at least `2/3`, and when
it is `0` every strategy is accepted with probability at most `1/3`; the value (maximum over provers)
of a finite public-coin game is attained, so this is the paper's "value at least `2/3` / at most
`1/3`". Valid instances are the exact ones (`MantriCVQ.Valid`). The number of communication slots is
`V.S (1^n)`, empty slots included. -/
theorem theorem_B_4 (d : ℕ) (a : ℝ) (ha : 1 ≤ a) :
    ∃ n₀ : ℕ, ∀ C : CodeDeg d, ∀ n h : ℕ, n₀ ≤ n → h ≤ hmax n → 42 * a ≤ (h : ℝ) →
      ∀ V : PCVerifier,
        ((∀ (O : Oracle) (tr : List Str), Conforms V (unary n) tr →
            (V.D.result O (tup (unary n :: tr)) ⌊(n : ℝ) ^ a⌋₊).isSome ∨
              V.qD.eval (tup (unary n :: tr)).length ≤ ⌊(n : ℝ) ^ a⌋₊) ∨
          ((∀ i : ℕ, i < V.S (unary n) → V.proverSlot (unary n) i = true →
              (V.len (unary n) i : ℝ) ≤ 2 * (n : ℝ) ^ a) ∧
            ∀ (O : Oracle) (tr : List Str), Conforms V (unary n) tr →
              queryCount V.D O (tup (unary n :: tr))
                (V.qD.eval (tup (unary n :: tr)).length) ≤ ⌊(n : ℝ) ^ a⌋₊)) →
        ∀ O₀ : Oracle,
        (∀ Y : Str → Bool, Valid C.code (dimsRange n 0 h) Y [] →
          (nodeVal C.code (dimsRange n 0 h) Y [] = true →
            ∃ σ : Strategy, (2 : ℝ) / 3 ≤ acceptProb (leafOracle O₀ n h Y) V σ (unary n)) ∧
          (nodeVal C.code (dimsRange n 0 h) Y [] = false →
            ∀ σ : Strategy, acceptProb (leafOracle O₀ n h Y) V σ (unary n) ≤ 1 / 3)) →
        (h : ℝ) / (14 * a) ≤ (V.S (unary n) : ℝ) := by sorry

end MantriCVQ.Supplement
