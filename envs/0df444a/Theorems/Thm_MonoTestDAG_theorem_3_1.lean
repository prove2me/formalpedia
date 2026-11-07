-- Prove2me | Theorems.Thm_MonoTestDAG_theorem_3_1
-- name    : MonoTestDAG.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:41.565896+00:00
-- url     : https://prove2.me/theorems/1ce92902-5ac8-40ea-9e7a-0e9ee71d922b
-- title:
--   Theorem 3.1 — Algorithm 1 is a one-sided tester with $O(m^{1/3}/\varepsilon^{2/3})$ queries
-- statement:
--   Let $G=(V,E)$ be a transitively reduced DAG and $m:=|E|$. There is an absolute constant $C>0$ such that for every $\varepsilon>0$, Algorithm 1 with sample size $q=\lfloor C\,m^{1/3}/\varepsilon^{2/3}\rfloor$ is an $\varepsilon$-tester with one-sided error. It queries at most $4q$ vertices, and
--   $$
--   q\le C\,\frac{m^{1/3}}{\varepsilon^{2/3}}.
--   $$
--   This tester supplies the term $c/3$ of the exponent $u(c,d)$.
--
--   Differences from the source:
--   - encoding: q ← Θ(m^{1/3}/ε^{2/3}) → q = ⌊C m^{1/3}/ε^{2/3}⌋ with the theorem's ∃ C; reason: a floor keeps the O(·) true for large ε, where the bound tends to 0 and no function is ε-far; m = 0 gives q = 0
--   - encoding: m := |E| → `numTR E`; reason: equal for a transitively reduced DAG
--   - encoding: at most 4q vertices is said in the proof, p.11 → a clause of the statement; reason: this is how the O(·) query complexity is obtained
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
--   - encoding: one-sided error: "always accepts" / "with probability 1" → acceptance probability 1; reason: §2.4 prints both; probability 1 is the form in the completeness requirement
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Theorem 3.1, p.11, with Algorithm 1, p.12

import Mathlib
import Definitions.Def_MonoTestDAG_alg1

namespace MonoTestDAG

/-- **Theorem 3.1.** Let `G = (V, E)` be a transitively reduced DAG and `m := |E|`. Algorithm 1 is
a tester for monotonicity with one-sided error and query complexity `O(m^{1/3}/ε^{2/3})`: there is
an absolute constant `C > 0` such that, run with `q = ⌊C m^{1/3}/ε^{2/3}⌋`, Algorithm 1 is a
one-sided `ε`-tester for every `ε > 0`, and it queries at most `4q` vertices.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Theorem 3.1, p.11, with Algorithm 1, p.12.

**Formalization Note.** "`q ← Θ(m^{1/3}/ε^{2/3})`" is `q = ⌊C m^{1/3}/ε^{2/3}⌋` for the constant
`C` of the statement. `m` is `numTR E`, which equals `|E|` for a transitively reduced DAG. -/
theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (E : V → V → Prop), IsDAG E →
      IsTransReduced E → ∀ ε : ℝ, 0 < ε →
        IsOneSidedTester E ε (alg1 E C ε) ∧
        (alg1 E C ε).QueriesAtMost (4 * (alg1Size E C ε : ℝ)) ∧
        (alg1Size E C ε : ℝ) ≤ C * (numTR E : ℝ) ^ ((1 : ℝ) / 3) / ε ^ ((2 : ℝ) / 3) := by sorry

end MonoTestDAG
