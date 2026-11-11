-- Prove2me | Theorems.Thm_OptQJunta_lemma_4_9
-- name    : OptQJunta.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:45.218585+00:00
-- url     : https://prove2.me/theorems/8bf340f8-f5b4-4802-bc11-0ab850467f78
-- title:
--   Lemma 4.9 — parity-address lower bound: more than $\sqrt{h/\varepsilon}/128$ controlled queries
-- statement:
--   Let $k,h,n$ be integers with $1\le h\le k$ and $n\ge k+h$, and let $0<\varepsilon\le1/8$ satisfy $16h2^h\le\varepsilon2^k$. Every tester for Problem 4.1 (with parameters $n,k,\varepsilon$) requires more than
--
--   $$
--   \frac{\sqrt{h/\varepsilon}}{128}
--   $$
--
--   queries in the worst case, even with controlled queries.
--
--   It is the main case of Theorem 4.8, where the logarithmic term appears.
--
--   Differences from the source:
--   - encoding: controlled queries → a query register `Option (Qubits n) × Bool` whose extra configuration "not querying" is left unchanged by the oracle; reason: the standard way to fold the control into the query; plain algorithms are the special case that never uses it
--   - encoding: a tester with ancillas, private randomness, intermediate measurements and adaptivity, whose query count is the largest over all inputs and executions (§2.5, p.22) → a `QAlgorithms.QueryAlg`: an oracle-independent unit start state, exactly $T$ standard queries $|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$ interleaved with oracle-independent unitaries on an arbitrary finite workspace, and an output read from the final computational-basis measurement; reason: deferred measurement, purification of the private randomness and padding of shorter executions turn every tester of the source into one of this form with the same output law on every input, and conversely
--   - encoding: $\mathrm{dist}_{\mathcal B}(f,\mathcal B_k)\ge\varepsilon$ (a minimum, Definition 2.14) → `IsFar f k ε`: $\varepsilon\le\mathrm{dist}_{\mathcal B}(f,g)$ for every $k$-junta $g$; reason: the minimum over the finite nonempty set $\mathcal B_k$ is at least $\varepsilon$ exactly when every element is
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Lemma 4.9, p.60

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OptQJunta_TestsJunta

open QAlgorithms

namespace OptQJunta

/-- **Lemma 4.9** (Parity-address lower bound; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.60). Let `k, h, n` be integers with
`1 ≤ h ≤ k` and `n ≥ k + h`, and let `0 < ε ≤ 1/8` satisfy `16h2^h ≤ ε2^k`. Every tester for Problem
4.1 requires more than `√(h/ε)/128` queries in the worst case, even with controlled queries.

**Formalization Note** Testers are query algorithms with controlled queries (`CTestsJunta`: query
register `Option (Qubits n) × Bool`, oracle `ctrlOracle f`, any finite workspace), which contain the
plain ones; "more than" is strict. -/
theorem lemma_4_9 (k h n : ℕ) (hh : 1 ≤ h) (hhk : h ≤ k) (hn : k + h ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 8) (hk : 16 * (h : ℝ) * 2 ^ h ≤ ε * 2 ^ k) (W : Type) [Fintype W] [DecidableEq W]
    (T : ℕ) (A : QueryAlg (Option (Qubits n)) Bool W T)
    (out : (Option (Qubits n) × Bool) × W → Bool) (hA : CTestsJunta A out k ε) :
    Real.sqrt (h / ε) / 128 < T := by sorry

end OptQJunta
