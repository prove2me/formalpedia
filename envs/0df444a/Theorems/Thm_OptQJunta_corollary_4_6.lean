-- Prove2me | Theorems.Thm_OptQJunta_corollary_4_6
-- name    : OptQJunta.corollary_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:21:23.296961+00:00
-- url     : https://prove2.me/theorems/dac3132e-b921-44ad-81ca-582f7a1253e3
-- title:
--   Corollary 4.6 — exact support recovery of a $k$-junta with $O(2^{k/2})$ queries
-- statement:
--   Fix integers $1\le k\le n$. Given query access to a Boolean function $f:\{0,1\}^n\to\{0,1\}$ promised to depend on at most $k$ coordinates, there is a quantum algorithm that outputs $\mathrm{supp}(f)$ with probability at least $2/3$ using $O(2^{k/2})$ queries:
--
--   $$
--   |\mathrm{supp}(f)|\le k\ \Longrightarrow\ \Pr[\text{output}=\mathrm{supp}(f)]\ge\tfrac23,\qquad T\le C\,2^{k/2},
--   $$
--
--   with an absolute constant $C$.
--
--   This is the branch of Theorem 4.2 used when $2^{n/2}$ is the smaller term.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ in the query bound → an explicit absolute constant chosen before every parameter of the statement; reason: the standard meaning of the asymptotic notation; §4 calls its constants absolute (Lemma 4.5, p.56)
--   - encoding: a tester with ancillas, private randomness, intermediate measurements and adaptivity, whose query count is the largest over all inputs and executions (§2.5, p.22) → a `QAlgorithms.QueryAlg`: an oracle-independent unit start state, exactly $T$ standard queries $|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$ interleaved with oracle-independent unitaries on an arbitrary finite workspace, and an output read from the final computational-basis measurement; reason: deferred measurement, purification of the private randomness and padding of shorter executions turn every tester of the source into one of this form with the same output law on every input, and conversely
--   - encoding: "promised to depend on at most $k$ coordinates" → $|\mathrm{supp}(f)|\le k$; reason: a function depends exactly on its relevant coordinates
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Corollary 4.6, p.57

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OptQJunta_infl

open QAlgorithms

namespace OptQJunta

/-- **Corollary 4.6** (Exact support recovery; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.57). Fix integers `1 ≤ k ≤ n`. Given query
access to a Boolean function `f : {0,1}^n → {0,1}` promised to depend on at most `k` coordinates,
there is a quantum algorithm that outputs `supp(f)` with probability at least `2/3` using `O(2^{k/2})`
queries.

**Formalization Note** The constant `C` is absolute. "Depends on at most `k` coordinates" is
`|supp f| ≤ k`. The algorithm is a `QAlgorithms.QueryAlg` (standard queries, unitary form) whose
output is a set `out z ⊆ [n]` read from the final measurement. -/
theorem corollary_4_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ k n : ℕ, 1 ≤ k → k ≤ n →
      ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (T : ℕ)
        (A : QueryAlg (Qubits n) Bool W T) (out : (Qubits n × Bool) × W → Finset (Fin n)),
        (T : ℝ) ≤ C * (2 : ℝ) ^ ((k : ℝ) / 2) ∧
        ∀ f : Qubits n → Bool, (supp f).card ≤ k →
          2 / 3 ≤ A.outputProb (xorOracle f) out (supp f) := by sorry

end OptQJunta
