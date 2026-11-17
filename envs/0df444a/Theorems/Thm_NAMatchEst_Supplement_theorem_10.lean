-- Prove2me | Theorems.Thm_NAMatchEst_Supplement_theorem_10
-- name    : NAMatchEst.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:43:54.506241+00:00
-- url     : https://prove2.me/theorems/ac3d5f44-f181-4754-afb1-63ef312c44d1
-- title:
--   Theorem 10 — path sampling distinguishes the §7 hard distributions with $O_{r,\alpha'}((n')^{2-1/(r+1)})$ queries
-- statement:
--   Fix an integer $r\ge2$ and a real $\alpha'\ge1$. Use the parameters of §7.7: an integer $\alpha$ with $8(r+1)\alpha'\le\alpha\le9(r+1)\alpha'$, $t=\lfloor n'/(2(\alpha+r+1))\rfloor$, $h=h_{r-1}$, and suppose $t\ge4^{r+1}r^2(2h)^{2r}$. Let $\Lambda$ be a simple $t$-fold lift of the union of the yes and no templates of §7.1 with girth greater than $2r$, and let $F_Y$, $F_N$ be its yes and no cores. Let $P_L,P_R$ be disjoint public core label sets of size $(\alpha+r)t$ among the $n'$ input labels.
--
--   Then there is a constant $D$, depending only on $r$ and $\alpha'$, such that for all such $n'$, $\alpha$, $\Lambda$, $P_L$, $P_R$ there is a randomized non-adaptive algorithm which makes at most
--
--   $$
--   D\cdot(n')^{2-1/(r+1)}
--   $$
--
--   queries on every outcome of its randomness and which answers *yes* with probability at least $2/3$ on every input carrying a publicly labelled copy of $F_Y$ with padded core degree $t$, and *no* with probability at least $2/3$ on every input carrying such a copy of $F_N$ (every adjacency-list ordering). Every repaired padded graph of §7.1 obtained from $F_Y$ (resp. $F_N$), under every permitted public relabelling and every list ordering, is such an input.
--
--   The theorem shows that the lower bound of Theorem 9(ii) is tight for its hard distributions when the approximation factor is constant: a better lower bound needs different instances.
--
--   **Formalization Note** The algorithm may depend on the parameters, the public label sets and the fixed lift.
--
--   Differences from the source:
--   - generalization: every repaired padded graph obtained from F_Y or F_N (padding outcome in the event 𝒢 followed by the deterministic repair), with any permitted public relabelling and any adjacency-list ordering → every G : AdjList n′ with IsCoreCopy: an injective side-preserving labelling of the core into PL, PR under which G restricted to the core labels is F, and every core label has degree t; reason: every repaired padded graph satisfies IsCoreCopy (sparse edges kept, all other edges have a dummy endpoint, core degree t, pp.94–95), so the Lean class contains the paper's; Algorithm 5 reads only complete core rows and discards non-core labels, so its analysis applies to the whole class
--   - generalization: the public information: the bipartition, the isolated labels and the four core and dummy label sets → only the core label sets PL, PR; reason: less public information makes the existence claim stronger; Algorithm 5 uses only the core label sets
--   - reading: O_{r,α′}((n′)^{2−1/(r+1)}) → D · n′^{2−1/(r+1)} with D depending only on r and α′, for every n′; reason: the constant of O_{r,α′}; Algorithm 5 step (1) covers small n′
--   - encoding: the cores are fixed graphs: a simple t-fold lift of the union of the templates with girth > 2r → Λ : TemplateLift α r t with (2r : ℕ∞) < egirth of Λ.graph univ; F_Y = Λ.graph {0, 2}, F_N = Λ.graph {1, 2}; A chosen after Λ; reason: the construction of §7.1 with the lift as data
--   - encoding: a simple graph on n vertices with its adjacency lists in some order → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every list ordering is an AdjList; same instances
--   - generalization: there is a randomized non-adaptive algorithm → there is a RandAlg (finite seed space with real weights, queries a function of the seed); reason: a RandAlg is a randomized non-adaptive algorithm, so the Lean statement implies the source's
--   - generalization: worst-case number of queries, identical queries answered once (p.20) → CostLE: the query list on every seed, every repetition charged; reason: a bound on the charged count on every seed implies the source's bound
--   - encoding: distinguishes the two promised cases → Bool output, true = the large-matching case; on graphs in neither case no requirement; reason: the paper's gap-tester convention (p.76)
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 10, p.119 (PDF 123); construction §7.1, pp.92–95 (PDF 96–99); parameters §7.7, p.115 (PDF 119); Algorithm 5, p.123 (PDF 127)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_Supplement_HINode
import Definitions.Def_NAMatchEst_Supplement_hSeq
import Definitions.Def_NAMatchEst_Supplement_TemplateLift
import Definitions.Def_NAMatchEst_Supplement_TemplateLift_graph
import Definitions.Def_NAMatchEst_Supplement_IsCoreCopy

namespace NAMatchEst.Supplement

/-- **Theorem 10.** Fix an integer `r ⩾ 2` and a constant approximation factor `α′ ⩾ 1`, and use
the parameters in Section 7.7. There is a randomized non-adaptive adjacency-list algorithm that
distinguishes the yes and no hard distributions with probability at least `2/3` in each case using
`O_{r,α′}((n′)^{2−1/(r+1)})` queries in the worst case. The algorithm is given the same public
information as in the lower bound. Its guarantee holds for every repaired padded graph obtained from
either fixed core, with any permitted public relabeling and any adjacency-list ordering.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Theorem 10, p.119 (PDF 123); construction §7.1, pp.92–95 (PDF 96–99); parameters §7.7,
p.115 (PDF 119); Algorithm 5 and proof, p.123 (PDF 127).

**Formalization Note**
1. Parameters (§7.7): an integer `α` with `8(r+1)α′ ⩽ α ⩽ 9(r+1)α′`, `t = ⌊n′/(2(α+r+1))⌋`,
   `h = h_{r−1}` (`hSeq`), the lift condition `t ⩾ 4^{r+1} r² (2h)^{2r}` (p.93), and a simple
   `t`-fold lift `Λ` of the union of the templates with girth `> 2r`; `F_Y = Λ.graph {0, 2}`,
   `F_N = Λ.graph {1, 2}`. The constant `D` of `O_{r,α′}` depends only on `r` and `α′`.
2. Public information: the core label sets `PL`, `PR` (disjoint, of size `n/2 = (α+r)t`). The
   algorithm may also depend on the fixed lift ("the cores are fixed graphs", p.92).
3. The guarantee is required on every input carrying a publicly labelled copy of `F_Y` (answer
   `true` = yes) or of `F_N` (answer `false` = no) with core degree `t` (`IsCoreCopy`). Every
   repaired padded graph, under every permitted relabelling and every adjacency-list ordering, is
   such an input, so this class contains the paper's.
4. Worst-case cost on every seed, repetitions charged (`CostLE`). -/
theorem theorem_10 : ∀ r : ℕ, 2 ≤ r → ∀ α' : ℝ, 1 ≤ α' → ∃ D : ℝ,
    ∀ (n' α t : ℕ), 8 * ((r : ℝ) + 1) * α' ≤ α → (α : ℝ) ≤ 9 * ((r : ℝ) + 1) * α' →
      t = n' / (2 * (α + r + 1)) →
      4 ^ (r + 1) * r ^ 2 * (2 * hSeq α (r - 1)) ^ (2 * r) ≤ t →
      ∀ Λ : TemplateLift α r t, (((2 * r : ℕ)) : ℕ∞) < (Λ.graph Finset.univ).egirth →
      ∀ PL PR : Finset (Fin n'), Disjoint PL PR →
        PL.card = (α + r) * t → PR.card = (α + r) * t →
        ∃ A : RandAlg n' Bool,
          A.CostLE (D * (n' : ℝ) ^ ((2 : ℝ) - 1 / ((r : ℝ) + 1))) ∧
          (∀ G : AdjList n', IsCoreCopy (Λ.graph {0, 2}) PL PR G →
            2 / 3 ≤ A.prob G (fun b => b = true)) ∧
          (∀ G : AdjList n', IsCoreCopy (Λ.graph {1, 2}) PL PR G →
            2 / 3 ≤ A.prob G (fun b => b = false)) := by sorry

end NAMatchEst.Supplement
