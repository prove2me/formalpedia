-- Prove2me | Theorems.Thm_OptQJunta_theorem_4_2
-- name    : OptQJunta.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:31.102904+00:00
-- url     : https://prove2.me/theorems/03ae52e6-93e5-42bc-b02d-13e187ad2cf1
-- title:
--   Theorem 4.2 — upper bound $O(\min\{2^{n/2},\sqrt{(1+\log_{2,+}(\varepsilon2^k))/\varepsilon}\})$ for Junta Boolean Testing
-- statement:
--   Fix integers $1\le k<n$ and $0<\varepsilon\le1/8$. Given query access to a Boolean function $f:\{0,1\}^n\to\{0,1\}$, there is a quantum algorithm that distinguishes $f\in\mathcal B_k$ from $\mathrm{dist}_{\mathcal B}(f,\mathcal B_k)\ge\varepsilon$ with success probability at least $2/3$ and uses
--
--   $$
--   O\Bigl(\min\Bigl\{2^{n/2},\ \sqrt{\frac{1+\log_{2,+}(\varepsilon2^k)}{\varepsilon}}\Bigr\}\Bigr)
--   $$
--
--   queries. Precisely: there is an absolute constant $C>0$ such that for all such $k,n,\varepsilon$ some tester for Problem 4.1, with some finite workspace, uses at most $C$ times this minimum.
--
--   This is the upper half of the paper's tight bound; together with Theorem 4.8 it gives Theorem 1.1.
--
--   Differences from the source:
--   - reading: $O(\cdot)$ in the query bound → an explicit absolute constant chosen before every parameter of the statement; reason: the standard meaning of the asymptotic notation; §4 calls its constants absolute (Lemma 4.5, p.56)
--   - encoding: a tester with ancillas, private randomness, intermediate measurements and adaptivity, whose query count is the largest over all inputs and executions (§2.5, p.22) → a `QAlgorithms.QueryAlg`: an oracle-independent unit start state, exactly $T$ standard queries $|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$ interleaved with oracle-independent unitaries on an arbitrary finite workspace, and an output read from the final computational-basis measurement; reason: deferred measurement, purification of the private randomness and padding of shorter executions turn every tester of the source into one of this form with the same output law on every input, and conversely
--   - encoding: $\mathrm{dist}_{\mathcal B}(f,\mathcal B_k)\ge\varepsilon$ (a minimum, Definition 2.14) → `IsFar f k ε`: $\varepsilon\le\mathrm{dist}_{\mathcal B}(f,g)$ for every $k$-junta $g$; reason: the minimum over the finite nonempty set $\mathcal B_k$ is at least $\varepsilon$ exactly when every element is
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 4.2, p.55

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OptQJunta_TestsJunta

open QAlgorithms

namespace OptQJunta

/-- **Theorem 4.2** (Upper bound for Junta Boolean Testing; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.55). Fix integers `1 ≤ k < n`
and `0 < ε ≤ 1/8`. Given query access to a Boolean function `f : {0,1}^n → {0,1}`, there is a
quantum algorithm that distinguishes `f ∈ ℬ_k` from `dist_ℬ(f, ℬ_k) ≥ ε` with success probability at
least `2/3` and uses `O(min{2^{n/2}, √((1 + log₂,₊(ε2^k))/ε)})` queries.

**Formalization Note** `O` is an absolute constant `C > 0` fixed before `k`, `n`, `ε`; the bound is
`juntaBound n k ε` (the radical covers the whole fraction, `log₂,₊ x = max{0, log₂ x}`). The tester
is a `QAlgorithms.QueryAlg` in unitary form with an existentially chosen finite workspace. -/
theorem theorem_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ k n : ℕ, 1 ≤ k → k < n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 8 →
      ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (T : ℕ)
        (A : QueryAlg (Qubits n) Bool W T) (out : (Qubits n × Bool) × W → Bool),
        TestsJunta A out k ε ∧ (T : ℝ) ≤ C * juntaBound n k ε := by sorry

end OptQJunta
