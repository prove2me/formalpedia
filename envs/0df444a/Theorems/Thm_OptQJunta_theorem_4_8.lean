-- Prove2me | Theorems.Thm_OptQJunta_theorem_4_8
-- name    : OptQJunta.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:31.582108+00:00
-- url     : https://prove2.me/theorems/b31cbb0e-b4b6-4d9c-959f-bd2ffe55a4d8
-- title:
--   Theorem 4.8 — lower bound $\Omega(\min\{2^{n/2},\sqrt{(1+\log_{2,+}(\varepsilon2^k))/\varepsilon}\})$ for Junta Boolean Testing
-- statement:
--   Fix integers $k\ge1$ and $n\ge2k$, and fix $0<\varepsilon\le1/8$. Any tester that, given query access to a Boolean function $f:\{0,1\}^n\to\{0,1\}$, distinguishes $f\in\mathcal B_k$ from $\mathrm{dist}_{\mathcal B}(f,\mathcal B_k)\ge\varepsilon$ with success probability at least $2/3$ requires
--
--   $$
--   \Omega\Bigl(\min\Bigl\{2^{n/2},\ \sqrt{\frac{1+\log_{2,+}(\varepsilon2^k)}{\varepsilon}}\Bigr\}\Bigr)
--   $$
--
--   queries: there is an absolute $c>0$ such that every tester, with any finite workspace, makes at least $c$ times this minimum.
--
--   It shows that Theorem 4.2 is optimal; with Theorem 4.2 it gives Theorem 1.1.
--
--   Differences from the source:
--   - reading: $\Omega(\cdot)$ in the query bound → an explicit absolute constant chosen before every parameter of the statement; reason: the standard meaning of the asymptotic notation; §4 calls its constants absolute (Lemma 4.5, p.56)
--   - encoding: a tester with ancillas, private randomness, intermediate measurements and adaptivity, whose query count is the largest over all inputs and executions (§2.5, p.22) → a `QAlgorithms.QueryAlg`: an oracle-independent unit start state, exactly $T$ standard queries $|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$ interleaved with oracle-independent unitaries on an arbitrary finite workspace, and an output read from the final computational-basis measurement; reason: deferred measurement, purification of the private randomness and padding of shorter executions turn every tester of the source into one of this form with the same output law on every input, and conversely
--   - encoding: $\mathrm{dist}_{\mathcal B}(f,\mathcal B_k)\ge\varepsilon$ (a minimum, Definition 2.14) → `IsFar f k ε`: $\varepsilon\le\mathrm{dist}_{\mathcal B}(f,g)$ for every $k$-junta $g$; reason: the minimum over the finite nonempty set $\mathcal B_k$ is at least $\varepsilon$ exactly when every element is
--   - encoding: bits $\{0,1\}$, coordinates $[n]=\{1,\dots,n\}$ → bits `Bool` (`QAlgorithms.Qubits n = Fin n → Bool`), coordinates `Fin n` from $0$; reason: a relabelling; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 4.8, p.59

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OptQJunta_TestsJunta

open QAlgorithms

namespace OptQJunta

/-- **Theorem 4.8** (Lower bound for Junta Boolean Testing; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.59). Fix integers `k ≥ 1` and
`n ≥ 2k`, and fix `0 < ε ≤ 1/8`. Any tester that, given query access to a Boolean function
`f : {0,1}^n → {0,1}`, distinguishes `f ∈ ℬ_k` from `dist_ℬ(f, ℬ_k) ≥ ε` with success probability at
least `2/3` requires `Ω(min{2^{n/2}, √((1 + log₂,₊(ε2^k))/ε)})` queries.

**Formalization Note** `Ω` is an absolute constant `c > 0` fixed before `k`, `n`, `ε`; the bound is
`juntaBound n k ε`. Every tester (`TestsJunta`), with any finite workspace, is covered. -/
theorem theorem_4_8 :
    ∃ c : ℝ, 0 < c ∧ ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 8 →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Qubits n) Bool W T)
        (out : (Qubits n × Bool) × W → Bool), TestsJunta A out k ε → c * juntaBound n k ε ≤ T := by sorry

end OptQJunta
