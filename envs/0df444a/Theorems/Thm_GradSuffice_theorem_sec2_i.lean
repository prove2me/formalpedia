-- Prove2me | Theorems.Thm_GradSuffice_theorem_sec2_i
-- name    : GradSuffice.theorem_sec2_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:49.177594+00:00
-- url     : https://prove2.me/theorems/1d7f45ab-8717-467d-b2d7-100610c01d5f
-- title:
--   §2 Theorem (i), p.6 — $\mathcal R^{(s)}_m(B)\le Cm^{-1/q}$ gives M-type $p$ for every $1<p<q/(q-1)$
-- statement:
--   Let $B$ be the unit ball of a Banach space $X$ and $B^\star$ its dual unit ball. Suppose that for some $C\ge1$ and $q\ge2$,
--   $$\mathcal R^{(s)}_m(B)\le C\,m^{-1/q}\qquad\text{for every } m\ge1 .$$
--
--   **Theorem, item (i).** For every $1<p<q/(q-1)$, $B^\star$ has M-type $p$ with a constant $K_p$ that depends only on $p$, $q$ and $C$.
--
--   This is the implication 3 → 4 of Theorem 1, due to Srebro, Sridharan and Tewari; Appendix A explains why their argument applies without compactness assumptions.
--
--   Differences from the source:
--   - encoding: R⁽ˢ⁾ₘ(B) ≤ C m^{−1/q} for every m ≥ 1 → seqRad ξ ≤ C m^{−1/q} for every m ≥ 1 and every B⋆-valued adaptive sequence ξ of length m; reason: a supremum is bounded by a number iff every element is
--   - encoding: K_p depends on p, q and C → ∃ K chosen after p, q, C and before the space X; reason: quantifier form of the dependence
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, unnumbered Theorem, item (i), p.6 ([45, Theorem 4 and Lemma 5]; App. A, p.36)

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_seqRad
import Definitions.Def_GradSuffice_HasMType

namespace GradSuffice

/-- **§2 Theorem, item (i) (Rademacher decay gives M-type).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, unnumbered Theorem, p.6
(after Srebro–Sridharan–Tewari [45, Theorem 4 and Lemma 5]; App. A, p.36): "Let `B` be the unit ball
of a Banach space, and `B⋆` its dual unit ball. Suppose that for some `C ≥ 1` and `q ≥ 2`, the
sequential Rademacher complexity satisfies `R⁽ˢ⁾ₘ(B) ≤ C m^{−1/q}` for every `m ≥ 1`. Then: (i) For every
`1 < p < q/(q − 1)`, `B⋆` has M-type `p` with constant `K_p` that depends on `p`, `q` and `C`."

**Formalization Note.** `K_p` is chosen after `p, q, C` and before the space. The hypothesis is
stated for every `B⋆`-valued adaptive sequence of every length `m ≥ 1`. -/
theorem theorem_sec2_i :
    ∀ C q : ℝ, 1 ≤ C → 2 ≤ q → ∀ p : ℝ, 1 < p → p < q / (q - 1) →
      ∃ K : ℝ, ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
        (∀ m : ℕ, 1 ≤ m → ∀ ξ : NondualOpt.Tree (StrongDual ℝ X) m, IsDualValued ξ →
          seqRad ξ ≤ C * (m : ℝ) ^ (-1 / q)) →
        HasMType X p K := by sorry

end GradSuffice
