-- Prove2me | Theorems.Thm_MonoTestDAG_theorem_3_2
-- name    : MonoTestDAG.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:43.40042+00:00
-- url     : https://prove2.me/theorems/4455e382-986d-4a72-bb0d-73973ae37a3e
-- title:
--   Theorem 3.2 — a one-sided tester with $O(\sqrt{m\ell}/(\varepsilon n))$ queries
-- statement:
--   Let $G=(V,E)$ be a transitively reduced DAG, with $n:=|V|$, $m:=|E|$ and $\ell:=|E(\mathrm{TC}(G))|$. There is an absolute constant $C>0$ such that for every $\varepsilon>0$ there is a non-adaptive tester for monotonicity of functions $f:V\to\mathbb R$ with one-sided error making at most
--   $$
--   C\,\frac{\sqrt{m\ell}}{\varepsilon n}
--   $$
--   queries. This tester supplies the term $(c+d)/2-1$ of the exponent $u(c,d)$.
--
--   Differences from the source:
--   - encoding: m := |E| → `numTR E`; reason: equal for a transitively reduced DAG
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
--   - encoding: O(·) / query complexity → an absolute constant C before the graph and ε, with the bound on every seed; reason: the paper counts worst-case queries
--   - encoding: one-sided error: "always accepts" / "with probability 1" → acceptance probability 1; reason: §2.4 prints both; probability 1 is the form in the completeness requirement
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Theorem 3.2, p.14

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_numTC
import Definitions.Def_MonoTestDAG_numTR

namespace MonoTestDAG

/-- **Theorem 3.2.** Let `G = (V, E)` be a transitively reduced DAG, `n := |V|`, `m := |E|` and
`ℓ := |E(TC(G))|`. For every `ε > 0` there is a non-adaptive tester for monotonicity of functions
`f : V → ℝ` with one-sided error and query complexity `O(√(mℓ)/(εn))`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Theorem 3.2, p.14.

**Formalization Note.** `O(·)` is an absolute constant `C` chosen before the graph and `ε`; the
query count is worst case. `m` is `numTR E`, which equals `|E|` for a transitively reduced DAG. -/
theorem theorem_3_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (E : V → V → Prop), IsDAG E →
      IsTransReduced E → ∀ ε : ℝ, 0 < ε → ∃ T : Tester V, IsOneSidedTester E ε T ∧
        T.QueriesAtMost (C * Real.sqrt ((numTR E : ℝ) * (numTC E : ℝ)) /
          (ε * (Fintype.card V : ℝ))) := by sorry

end MonoTestDAG
