-- Prove2me | Theorems.Thm_MonoTestDAG_Supplement_theorem_4_7
-- name    : MonoTestDAG.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:48:31.187568+00:00
-- url     : https://prove2.me/theorems/3c1088cd-a4de-42d8-821b-d134a5e93f68
-- title:
--   Theorem 4.7 — $\Omega(\sqrt{s})$ lower bound for non-adaptive testers with two-sided error
-- statement:
--   Let $\varepsilon\in(0,1/8]$, and let $U=(L,R;E)$ be any $(s,4\varepsilon)$-PMRS graph with $|L|=|R|=n_0$. Orient every edge from $L$ to $R$ to form the bipartite DAG $G=P(U)$. If $\varepsilon n_0$ is sufficiently large, then every randomized non-adaptive $\varepsilon$-tester for monotonicity on $G$, even with two-sided error, makes
--
--   $$
--   \Omega(\sqrt{s})
--   $$
--
--   queries in the worst case.
--
--   This converts a large edge-disjoint family of positive matchings into an information-theoretic lower bound for monotonicity testing.
--
--   **Formalization Note.** The constants hidden by $\Omega$ and by “sufficiently large” are absolute and are quantified before every graph instance. The published PMRS predicate at parameter $4\varepsilon$ already contains exactly the conditions $0<\varepsilon\le1/8$ and $|L|=|R|$.
--
--   Differences from the source:
--   - encoding: “$\varepsilon n_0$ is sufficiently large” and $\Omega(\sqrt{s})$ → absolute constants $K,C>0$ with $K\le\varepsilon|L|$ and $C\sqrt{s}\le q$ for every real worst-case query budget $q$; reason: this expands the two asymptotic phrases and represents the integer query count by an equivalent real upper bound
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Theorem 4.7, p.20 (PDF 22)

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_IsPMRSWitness

namespace MonoTestDAG.Supplement

/-- **Theorem 4.7 (Ω(√s) lower bound for non-adaptive testers with two-sided error).** Let
`ε ∈ (0,1/8]`, let `U = (L,R;E)` be any `(s,4ε)`-PMRS graph with `|L|=|R|=n₀`, and
put `G=P(U)`. If `εn₀` is sufficiently large, every randomized non-adaptive two-sided
`ε`-tester on `G` makes `Ω(√s)` queries.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Theorem 4.7, p.20.

**Formalization Note.** The positive constants `C` and `K` are absolute and precede every graph
instance. "Sufficiently large" is `K ≤ ε|L|`; `Ω(√s)` is the worst-case bound
`C√s ≤ q` for every real query budget `q`. -/
theorem theorem_4_7 :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ {L R : Type} [Fintype L] [Fintype R] (EU : Finset (L × R)) (ε : ℝ) (s : ℕ),
        IsPMRSGraph EU (4 * ε) s →
        K ≤ ε * (Fintype.card L : ℝ) →
        ∀ (T : Tester (L ⊕ R)) (q : ℝ), IsTwoSidedTester (bipDAG EU) ε T →
          T.QueriesAtMost q → C * Real.sqrt (s : ℝ) ≤ q := by sorry

end MonoTestDAG.Supplement
