-- Prove2me | Theorems.Thm_MonoTestDAG_Supplement_theorem_4_11
-- name    : MonoTestDAG.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:49:45.4052+00:00
-- url     : https://prove2.me/theorems/78a21065-57fb-42be-bb8a-28ed1f8e6fb7
-- title:
--   Theorem 4.11 — near-$\sqrt{n/\varepsilon}$ lower bounds with two-sided error
-- statement:
--   For every $\delta>0$ there is a constant $C_\delta>0$ such that, for every $\varepsilon\in(0,1/8]$, there are infinitely many integers $n$ and bipartite DAGs on $n$ vertices for which every randomized non-adaptive $\varepsilon$-tester for monotonicity, even with two-sided error, makes at least
--
--   $$
--   C_\delta\frac{n^{1/2-\delta}}{\sqrt{\varepsilon}}
--   $$
--
--   queries in the worst case.
--
--   Thus even the special class of height-two DAGs attains the general-poset square-root barrier up to an arbitrarily small loss in the exponent.
--
--   **Formalization Note.** The subscript in $\Omega_\delta$ is expanded by choosing $C_\delta$ before $\varepsilon$; the threshold implicit in “infinitely many” may depend on $\varepsilon$. A bipartite DAG is exhibited as $P(U)$ for a finite edge set $U\subseteq L\times R$; the tester is the published arbitrary-randomness, worst-case-query model.
--
--   Differences from the source:
--   - encoding: “fix $\varepsilon$,” “infinitely many $n$,” and $\Omega_\delta$ → for every $\delta$ a positive $C_\delta$ is chosen before $\varepsilon$, and for every threshold $N_0$ there is an integer $n\ge\max\{N_0,1\}$ and a graph; reason: this expands the subscripted asymptotic and infinitude notation, preserving that the hidden constant depends only on $\delta$ while excluding the real-power boundary at $n=0$
--   - encoding: a lower bound on the number of queries → the inequality is required for every real worst-case query budget $q$; reason: finite query counts are integers, so real upper bounds encode the same worst-case complexity without changing any tester instance
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Theorem 4.11, p.23 (PDF 25), proof p.24 (PDF 26)

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_bipDAG

namespace MonoTestDAG.Supplement

/-- **Theorem 4.11 (near-√(n/ε) lower bounds with two-sided error).** Uniformly for
`ε ∈ (0,1/8]`, every `δ>0` admits infinitely many `n` and bipartite `n`-vertex DAGs on
which every randomized non-adaptive two-sided `ε`-tester needs
`Ω_δ(n^(1/2-δ)/√ε)` queries.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Theorem 4.11, pp.23–24.

**Formalization Note.** The subscript in `Ω_δ` is made explicit by choosing the hidden positive
constant after `δ` but before `ε`; the threshold implicit in "infinitely many" may still depend on
`ε`. The displayed `1/√ε` dependence remains explicit. "Infinitely many `n`" is written as
`∀ N₀, ∃ n ≥ N₀`, with `n≥1` to exclude the real-power boundary at zero. The graph is exhibited
as `P(U)` for a finite bipartite edge set. -/
theorem theorem_4_11 :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 8 → ∀ N₀ : ℕ,
        ∃ (n : ℕ) (L R : Type) (_ : Fintype L) (_ : Fintype R)
          (EU : Finset (L × R)),
          N₀ ≤ n ∧ 1 ≤ n ∧ n = Fintype.card L + Fintype.card R ∧
          IsDAG (bipDAG EU) ∧
          ∀ (T : Tester (L ⊕ R)) (q : ℝ), IsTwoSidedTester (bipDAG EU) ε T →
            T.QueriesAtMost q →
            C * ((n : ℝ) ^ (1 / 2 - δ) / Real.sqrt ε) ≤ q := by sorry

end MonoTestDAG.Supplement
