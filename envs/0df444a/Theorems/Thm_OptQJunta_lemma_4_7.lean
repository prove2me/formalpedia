-- Prove2me | Theorems.Thm_OptQJunta_lemma_4_7
-- name    : OptQJunta.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:20:39.013864+00:00
-- url     : https://prove2.me/theorems/3d200811-22c8-44df-97b6-f143021045e2
-- title:
--   Lemma 4.7 — unique-search lower bound $\Omega(2^{m/2})$
-- statement:
--   For an integer $m\ge1$, distinguishing the zero function $g:\{0,1\}^m\to\{0,1\}$ from one with a unique marked input, with success probability at least $2/3$, requires $\Omega(2^{m/2})$ Boolean oracle queries: there is an absolute $c>0$ such that every quantum query algorithm that answers "zero" with probability at least $2/3$ on $g\equiv0$ and "marked" with probability at least $2/3$ on every $g$ with exactly one $x$ such that $g(x)=1$ makes at least $c\,2^{m/2}$ queries.
--
--   It covers the regime of small $n$ in Theorem 4.8.
--
--   Differences from the source:
--   - reading: $\Omega(\cdot)$ in the query bound → an explicit absolute constant chosen before every parameter of the statement; reason: the standard meaning of the asymptotic notation; §4 calls its constants absolute (Lemma 4.5, p.56)
--   - encoding: a tester with ancillas, private randomness, intermediate measurements and adaptivity, whose query count is the largest over all inputs and executions (§2.5, p.22) → a `QAlgorithms.QueryAlg`: an oracle-independent unit start state, exactly $T$ standard queries $|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$ interleaved with oracle-independent unitaries on an arbitrary finite workspace, and an output read from the final computational-basis measurement; reason: deferred measurement, purification of the private randomness and padding of shorter executions turn every tester of the source into one of this form with the same output law on every input, and conversely
--   - encoding: "distinguishing" (either answer convention) → output `false` on the zero function and `true` on unique-marked functions, each with probability at least $2/3$; reason: the other convention is the same algorithm with the output negated
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Lemma 4.7, p.59

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

open QAlgorithms

namespace OptQJunta

/-- **Lemma 4.7** (Unique-search lower bound [BBBV97]; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.59). For an integer `m ≥ 1`,
distinguishing the zero function `g : {0,1}^m → {0,1}` from one with a unique marked input, with
success probability at least `2/3`, requires `Ω(2^{m/2})` Boolean oracle queries.

**Formalization Note** `Ω` is an absolute constant `c > 0`. A distinguisher is a `QAlgorithms.QueryAlg`
(standard queries, any finite workspace) with an output bit that is `false` with probability `≥ 2/3`
on the zero function and `true` with probability `≥ 2/3` on every function with exactly one
`x` with `g(x) = 1`; the opposite labelling is the same algorithm with the output negated. -/
theorem lemma_4_7 :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 1 ≤ m →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Qubits m) Bool W T)
        (out : (Qubits m × Bool) × W → Bool),
        2 / 3 ≤ A.outputProb (xorOracle (fun _ : Qubits m => false)) out false →
        (∀ g : Qubits m → Bool, (∃! x, g x = true) →
          2 / 3 ≤ A.outputProb (xorOracle g) out true) →
        c * (2 : ℝ) ^ ((m : ℝ) / 2) ≤ T := by sorry

end OptQJunta
