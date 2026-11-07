-- Prove2me | Theorems.Thm_MonoTestDAG_fischer_tester
-- name    : MonoTestDAG.fischer_tester
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:50.920966+00:00
-- url     : https://prove2.me/theorems/d26f9c4e-87de-49c2-a3cd-5761d2b77f2e
-- title:
--   §1.1 — the classical $O(\min\{\sqrt{n/\varepsilon},\ell/(\varepsilon n)\})$ tester of Fischer et al.
-- statement:
--   There is an absolute constant $C>0$ such that for every DAG on $n$ vertices with $\ell$ comparable pairs and every $\varepsilon>0$, there is a non-adaptive $\varepsilon$-tester for monotonicity with one-sided error making at most
--   $$
--   C\min\Bigl\{\sqrt{n/\varepsilon},\ \frac{\ell}{\varepsilon n}\Bigr\}
--   $$
--   queries. Together with Theorems 3.1 and 3.2 this gives the upper bound of Theorem 1.1(i).
--
--   Differences from the source:
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
--   - encoding: O(·) / query complexity → an absolute constant C before the graph and ε, with the bound on every seed; reason: the paper counts worst-case queries
--   - encoding: one-sided error: "always accepts" / "with probability 1" → acceptance probability 1; reason: §2.4 prints both; probability 1 is the form in the completeness requirement
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §1.1, p.1 (citing [19])

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_numTC

namespace MonoTestDAG

/-- **The classical tester of Fischer et al. [19]** (cited in §1.1). There is an absolute constant
`C > 0` such that for every DAG `G = (V, E)` with `n = |V|` and `ℓ = |E(TC(G))|`, and every
`ε > 0`, there is a non-adaptive `ε`-tester for monotonicity with one-sided error making at most
`C · min{√(n/ε), ℓ/(εn)}` queries.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §1.1, p.1 (citing [19]).

**Formalization Note.** `O(·)` is an absolute constant `C` chosen before the graph and `ε`; the
query count is worst case over the tester's randomness. -/
theorem fischer_tester :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (E : V → V → Prop), IsDAG E →
      ∀ ε : ℝ, 0 < ε → ∃ T : Tester V, IsOneSidedTester E ε T ∧
        T.QueriesAtMost (C * min (Real.sqrt ((Fintype.card V : ℝ) / ε))
          ((numTC E : ℝ) / (ε * (Fintype.card V : ℝ)))) := by sorry

end MonoTestDAG
