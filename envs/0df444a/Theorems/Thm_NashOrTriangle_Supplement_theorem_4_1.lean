-- Prove2me | Theorems.Thm_NashOrTriangle_Supplement_theorem_4_1
-- name    : NashOrTriangle.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:49:35.416908+00:00
-- url     : https://prove2.me/theorems/2acccd72-d616-4021-9fae-313e35e40fd0
-- title:
--   Theorem 4.1 — every $1/k$-Nash equilibrium of a triangle-free parity game needs $\Omega(tk^2/\log k)$ rows, hence BR calls
-- statement:
--   **Theorem 4.1.** There are universal constants $C'>0$, $c>0$ and $K$ such that for all $k\ge K$ and all $t\ge C'\log k$ there is a finite binary game with no $t$-triangle with the following two properties.
--
--   1. Every $1/k$-Nash equilibrium $(p,q)$, over all mixed strategies of the game, has at least
--   $$c\,\frac{t k^2}{\log k}$$
--   distinct rows in the support of $p$.
--   2. Consequently, every algorithm needs that many BR calls, even with exact best responses and even if it is randomized: every halted run of any program of the oracle model, on any input memory and against any exact BR oracle, that ends with a correct answer to $\mathrm{NorT}(k,t)$ has made at least $c\,tk^2/\log k$ BR calls.
--
--   The theorem is the randomized lower bound of the paper: it is cubic in $k$ for $t$ of order $k$, against the exponential deterministic lower bound of Theorem 3.1.
--
--   **Formalization Note** $\Omega(\cdot)$ is one universal constant $c$ shared by both clauses and $\log$ is the natural logarithm. A randomized algorithm is covered because the clause holds for every input memory, that is for every realization of its random bits.
--
--   Differences from the source:
--   - encoding: Ω(tk²/log k), for all sufficiently large k → c·t·k²/Real.log k for one universal c > 0 in both clauses, for all k ≥ K with K universal; reason: standard meaning of Ω and of 'sufficiently large'
--   - encoding: every 1/k-Nash equilibrium → every pair of probability mass functions on the finite game satisfying the two Nash inequalities at 1/k; reason: §1.1: mixed strategies are countably additive distributions; on a finite game these are all probability vectors
--   - reading: every algorithm needs that many BR calls, even with exact best responses, and even if it is randomized → every halted run of every program on every input memory against every exact BR oracle that ends with IsNorTNashAnswer has at least that many BR calls; reason: a randomized algorithm is a program run on one realization of its bits; the per-run statement covers every realization and every exact oracle
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962cc2efb135d3833e902fa4e861e03acf9d2df3fe8140a50b646da66f7), Theorem 4.1, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_NashOrTriangle_OracleMachine
import Definitions.Def_NashOrTriangle_IsBinary
import Definitions.Def_NashOrTriangle_HasTriangle
import Definitions.Def_NashOrTriangle_Supplement_NashAnswer
import Definitions.Def_NashOrTriangle_Supplement_PMFGame

namespace NashOrTriangle.Supplement

/-- **Theorem 4.1** (a lower bound for randomized algorithms). There is a universal constant
`C′ > 0` such that for all sufficiently large `k` and all `t ≥ C′ log k`, there is a finite binary
game with no `t`-triangle in which every `1/k`-Nash equilibrium has at least `Ω(tk²/log k)`
distinct rows in its support. Consequently, every algorithm needs that many BR calls, even with
exact best responses, and even if it is randomized.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Theorem 4.1, printed p. 11 (PDF p. 12).

**Formalization Note** `Ω(tk²/log k)` is `c·t·k²/log k` for one universal `c > 0`, the same in
both clauses; "sufficiently large `k`" is `k ≥ K` for a universal `K`; `log` is `Real.log`.
Clause 1 ranges over all mixed strategies of the finite game (`PMF`, i.e. all probability
vectors), and the support size is the number of rows of positive probability. Clause 2 is the
consequence: every halted run of every program (real literals allowed), on every input memory
(this covers every realization of the random bits of a randomized algorithm), against every exact
BR oracle (adaptive ones included), that ends with a correct answer to `NorT(k, t)`
(`IsNorTNashAnswer`) has made at least that many BR calls. -/
theorem theorem_4_1 :
    ∃ C' c : ℝ, 0 < C' ∧ 0 < c ∧ ∃ K : ℕ, ∀ k t : ℕ, K ≤ k → C' * Real.log (k : ℝ) ≤ (t : ℝ) →
      ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (_ : Nonempty A) (_ : Nonempty B)
        (M : A → B → ℚ), IsBinary M ∧ ¬ HasTriangle M t ∧
        (∀ (p : PMF A) (q : PMF B), IsNashPMF M (1 / (k : ℝ)) p q →
          c * (t : ℝ) * (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ (p.support.ncard : ℝ)) ∧
        (∀ (P : Program) (x : ℤ → ℝ) (adv : BRAdversary M 0) (n : ℕ),
          (run P M adv x n).output.isSome → IsNorTNashAnswer M k t (run P M adv x n) →
          c * (t : ℝ) * (k : ℝ) ^ 2 / Real.log (k : ℝ) ≤ ((run P M adv x n).brCalls : ℝ)) := by sorry

end NashOrTriangle.Supplement
