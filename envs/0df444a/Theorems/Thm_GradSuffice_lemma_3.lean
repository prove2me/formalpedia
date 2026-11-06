-- Prove2me | Theorems.Thm_GradSuffice_lemma_3
-- name    : GradSuffice.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:22.56643+00:00
-- url     : https://prove2.me/theorems/4c87fa7d-42f7-4131-9949-df3af259ba73
-- title:
--   Lemma 3, p.24 — $\mathcal R^{(s)}_{m_0}(B;\xi)>Cm_0^{-1/q}$ yields a tree shattered at margin $1/10$ of depth $\ge\exp(cM)$
-- statement:
--   Let $B$ be the unit ball of a Banach space $X$ and $B^\star$ its dual unit ball.
--
--   **Lemma 3.** There are universal constants $c>0$ and $M_0>0$ with the following property. Suppose that for some $B^\star$-valued adaptive sequence $\xi=(\xi_1,\dots,\xi_{m_0})$, some $q\ge2$ and some $0<C\le1/2$,
--   $$\mathcal R^{(s)}_{m_0}(B;\xi)>C\,m_0^{-1/q},\tag{16}$$
--   and set $M:=\min\{q,\ \log m_0/\log(1/C)\}$. If $M\ge M_0$, there is a $B^\star$-valued binary tree, shattered by $B$ at margin $1/10$, whose depth $d$ satisfies
--   $$d\ \ge\ \exp(cM).$$
--
--   Lemma 3 is the quantitative form of Theorem 3 (take $C=1/e$).
--
--   Differences from the source:
--   - reading: "there exists a binary tree, shattered at margin 1/10" → a B⋆-valued tree shattered by B at margin 1/10; reason: Theorem 3, which Lemma 3 proves, states B⋆-valued and shattered by B, and the proof normalizes each node (p.26); without a bound on the labels any tree can be rescaled to any margin
--   - encoding: universal constants c, M₀ → ∃ c > 0, M₀ > 0 chosen before the space X; reason: quantifier form of "universal"
--   - reading: log (no base printed) → natural logarithm; reason: the proof uses λ = −log c₀ and exp; natural logarithm throughout
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Lemma 3, p.24, Eq. (16)

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_IsShattered
import Definitions.Def_GradSuffice_seqRad

namespace GradSuffice

/-- **Lemma 3 (quantitative form of Theorem 3).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Lemma 3, p.24: "Let `B` be the unit ball of a
Banach space and let `B⋆` be its dual unit ball. Suppose that, for some adaptive sequence
`ξ = (ξ₁, …, ξ_{m₀})` with values in `B⋆`, some `q ≥ 2`, and some `0 < C ≤ 1/2`,
`R⁽ˢ⁾_{m₀}(B; ξ) > C m₀^{−1/q}` (16). Set `M := min{q, log m₀ / log(1/C)}`. Then there exist universal
constants `c > 0` and `M₀ > 0` such that, whenever `M ≥ M₀`, there exists a binary tree, shattered at
margin `1/10`, whose depth `d` satisfies `d ≥ exp(cM)`."

**Formalization Note.** `c` and `M₀` are chosen before the space. The tree is `B⋆`-valued and
shattered by `B` (as in Theorem 3, which this lemma proves; a tree with unrestricted labels can be
rescaled to any margin). `log` is natural. -/
theorem lemma_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ M₀ : ℝ, 0 < M₀ ∧
      ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
        (m₀ : ℕ) (ξ : NondualOpt.Tree (StrongDual ℝ X) m₀), IsDualValued ξ →
      ∀ q C : ℝ, 2 ≤ q → 0 < C → C ≤ 1 / 2 →
        C * (m₀ : ℝ) ^ (-1 / q) < seqRad ξ →
        M₀ ≤ min q (Real.log m₀ / Real.log (1 / C)) →
        ∃ (d : ℕ) (ζ : NondualOpt.Tree (StrongDual ℝ X) d), IsDualValued ζ ∧
          IsShattered (Metric.closedBall (0 : X) 1) (1 / 10) ζ ∧
          Real.exp (c * min q (Real.log m₀ / Real.log (1 / C))) ≤ d := by sorry

end GradSuffice
