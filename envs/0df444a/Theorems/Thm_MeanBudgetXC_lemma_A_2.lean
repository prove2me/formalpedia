-- Prove2me | Theorems.Thm_MeanBudgetXC_lemma_A_2
-- name    : MeanBudgetXC.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:59.661878+00:00
-- url     : https://prove2.me/theorems/30bd2119-cd4b-4a26-b8ea-073bdf77291b
-- title:
--   Lemma A.2 — antiblocker and formulation size
-- statement:
--   Let $\iota$ be a finite index set with $m=|\iota|$.
--
--   1. If $K\subseteq\mathbb{R}^m_+$ is a compact convex down-closed set containing the origin, then $\mathrm{abl}(\mathrm{abl}(K))=K$.
--   2. If a nonempty polyhedral $K\subseteq\mathbb{R}^m_+$ has an extended formulation with $s$ inequalities, then its antiblocker has a formulation with at most $s+m+1$ inequalities.
--
--   The two parts carry a small formulation of the zero section over to the coefficient body.
--
--   **Formalization Note** "Down-closed" is $\downarrow K=K$, which also places $K$ in the nonnegative orthant.
--
--   Differences from the source:
--   - encoding: a nonempty polyhedral $K$ with an $s$-inequality extended formulation → a nonempty $K$ with `IsEFOfSize K s`, without a separate polyhedrality hypothesis; reason: a set with an extended formulation is a polyhedron, so the hypothesis is implied and no instance changes
--   - encoding: a formulation with at most $s+m+1$ inequalities → $\exists r\le s+m+1$ with `IsEFOfSize (abl K) r`; reason: this is the same bound; the platform definition counts exactly $r$ rows
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Lemma A.2, p.37

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_MeanBudgetXC_downClosure
import Definitions.Def_MeanBudgetXC_abl

namespace MeanBudgetXC

open ExtensionComplexity.TSP

/-- **Lemma A.2** (Antiblocker and formulation size) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget
Transition for Local Pair Marginals*, STOC 2027 submission, manuscript sha256 882d9c71…9e76,
Appendix A.1, p.37). (i) If `K ⊆ ℝ^m_+` is a compact convex down-closed set containing the
origin, then `abl(abl(K)) = K`. (ii) If a nonempty polyhedral `K ⊆ ℝ^m_+` has an `s`-inequality
extended formulation, its antiblocker has a formulation with at most `s + m + 1` inequalities.

**Formalization Note** `m = card ι`. "Down-closed" is `↓K = K`, which also places `K` in the
nonnegative orthant. In (ii) "polyhedral" is not a separate hypothesis: a set with an extended
formulation is a polyhedron. -/
theorem lemma_A_2 {ι : Type*} [Fintype ι] :
    (∀ K : Set (ι → ℝ), IsCompact K → Convex ℝ K → downClosure K = K → (0 : ι → ℝ) ∈ K →
        abl (abl K) = K) ∧
      ∀ (K : Set (ι → ℝ)) (s : ℕ), K.Nonempty → (∀ x ∈ K, 0 ≤ x) → IsEFOfSize K s →
        ∃ r ≤ s + Fintype.card ι + 1, IsEFOfSize (abl K) r := by sorry

end MeanBudgetXC
