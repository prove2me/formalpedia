-- Prove2me | Theorems.Thm_OptQJunta_theorem_1_1
-- name    : OptQJunta.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:28.419193+00:00
-- url     : https://prove2.me/theorems/fe9ff797-e254-4d15-87b6-df28fc9fc8c3
-- title:
--   Theorem 1.1 — testing $k$-juntas among $n$-bit Boolean functions takes $\Theta(\sqrt{k/\varepsilon})$ quantum queries for $n\ge2k$, $2^{-k/16}\le\varepsilon\le1/8$
-- statement:
--   For integers $k\ge1$ and $n\ge2k$, and for $2^{-k/16}\le\varepsilon\le1/8$, testing whether an $n$-bit Boolean function is a $k$-junta or is $\varepsilon$-far from every $k$-junta has quantum query complexity
--
--   $$
--   \Theta\bigl(\sqrt{k/\varepsilon}\bigr).
--   $$
--
--   Precisely: there are absolute constants $c,C>0$ such that for all such $k,n,\varepsilon$,
--
--   1. some tester for Problem 4.1 (success probability $2/3$ on every $k$-junta and on every $\varepsilon$-far function), with some finite workspace, makes at most $C\sqrt{k/\varepsilon}$ queries; and
--   2. every such tester, with any finite workspace, makes at least $c\sqrt{k/\varepsilon}$ queries.
--
--   This removes the $\log k$ gap between the tester of Ambainis, Belovs, Regev and de Wolf and the lower bound of Bun, Kothari and Thaler. The range of $\varepsilon$ is nonempty only for $k\ge48$, as stated in the source.
--
--   Differences from the source:
--   - reading: $\Theta(\cdot)$ in the query complexity → an explicit absolute constant chosen before every parameter of the statement; reason: the standard meaning of the asymptotic notation; §4 calls its constants absolute (Lemma 4.5, p.56)
--   - encoding: a tester with ancillas, private randomness, intermediate measurements and adaptivity, whose query count is the largest over all inputs and executions (§2.5, p.22) → a `QAlgorithms.QueryAlg`: an oracle-independent unit start state, exactly $T$ standard queries $|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$ interleaved with oracle-independent unitaries on an arbitrary finite workspace, and an output read from the final computational-basis measurement; reason: deferred measurement, purification of the private randomness and padding of shorter executions turn every tester of the source into one of this form with the same output law on every input, and conversely
--   - encoding: $\mathrm{dist}_{\mathcal B}(f,\mathcal B_k)\ge\varepsilon$ (a minimum, Definition 2.14) → `IsFar f k ε`: $\varepsilon\le\mathrm{dist}_{\mathcal B}(f,g)$ for every $k$-junta $g$; reason: the minimum over the finite nonempty set $\mathcal B_k$ is at least $\varepsilon$ exactly when every element is
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OptQJunta_TestsJunta

open QAlgorithms

namespace OptQJunta

/-- **Theorem 1.1** (Testing junta Boolean functions, informal version of Theorems 4.2 and 4.8; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…,
p.4). For integers `k ≥ 1` and `n ≥ 2k`, and for `2^{−k/16} ≤ ε ≤ 1/8`, testing whether an `n`-bit
Boolean function is a `k`-junta or is `ε`-far from every `k`-junta has quantum query complexity
`Θ(√(k/ε))`.

**Formalization Note** `Θ` is read with absolute constants `c, C > 0` chosen before `k`, `n`, `ε`:
(1) some tester (Problem 4.1, `TestsJunta`) with some finite workspace uses at most `C √(k/ε)`
queries, and (2) every tester, with any finite workspace, uses at least `c √(k/ε)` queries. Testers
are `QAlgorithms.QueryAlg`s with the standard query `|x, b⟩ ↦ |x, b ⊕ f(x)⟩` in unitary form
(deferred measurement, purified randomness, padded executions); success `2/3` is required only on
promised inputs. The regime is nonempty only for `k ≥ 48`, as printed. -/
theorem theorem_1_1 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n → ∀ ε : ℝ,
      (2 : ℝ) ^ (-(k : ℝ) / 16) ≤ ε → ε ≤ 1 / 8 →
      (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (T : ℕ)
          (A : QueryAlg (Qubits n) Bool W T) (out : (Qubits n × Bool) × W → Bool),
          TestsJunta A out k ε ∧ (T : ℝ) ≤ C * Real.sqrt (k / ε)) ∧
      (∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Qubits n) Bool W T)
          (out : (Qubits n × Bool) × W → Bool), TestsJunta A out k ε → c * Real.sqrt (k / ε) ≤ T) := by sorry

end OptQJunta
