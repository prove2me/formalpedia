-- Prove2me | Theorems.Thm_GradSuffice_Supplement_theorem_sec2_ii
-- name    : GradSuffice.Supplement.theorem_sec2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:27:22.113207+00:00
-- url     : https://prove2.me/theorems/107618e4-ade4-44a6-ad76-3f5a553fcb60
-- title:
--   §2 Theorem (ii), p.6 — $\mathcal R^{(s)}_m(B)\le Cm^{-1/q}$ gives a bounded $(K,q')$-uniformly convex regularizer for every $q'>q$
-- statement:
--   Let $B$ be the unit ball of a real Banach space $X$ and $B^\star$ its dual unit ball. Suppose that for some $C\ge1$ and $q\ge2$ the sequential Rademacher complexity satisfies
--   $$\mathcal R^{(s)}_m(B)\le C\,m^{-1/q}\qquad\text{for every } m\ge1.$$
--   Then for every $q'>q$ there is a continuous convex function $R$ with $0\le R(w)\le 1$ on $B$ that is $(K,q')$-uniformly convex:
--   $$R\Big(\frac{w_1+w_2}{2}\Big)\le\frac12R(w_1)+\frac12R(w_2)-\Big(\frac1K\Big)^{q'}\Big\|\frac{w_1-w_2}{2}\Big\|^{q'}\qquad(w_1,w_2\in B),$$
--   where $K>0$ depends only on $q$, $q'$ and $C$.
--
--   This is the regularizer that Mirror Descent uses in item (iii), and it gives the implication 3 → 5 of Theorem 1 with an explicit exponent.
--
--   **Formalization Note** $K$ is chosen after $C,q,q'$ and before the space. The hypothesis bounds $\mathcal R^{(s)}_m(B;\bar\xi)$ for every $B^\star$-valued adaptive sequence of every length $m\ge1$. The $(K,q')$ condition is the published `NondualOpt.IsUnifConvexOn` with constant $(1/(2K))^{q'}$, as in the base mission.
--
--   Differences from the source:
--   - encoding: R⁽ˢ⁾ₘ(B) ≤ C m^{−1/q} (a supremum over adaptive sequences) → seqRad ξ ≤ C m^{−1/q} for every B⋆-valued adaptive sequence ξ of every length m ≥ 1; reason: a supremum is at most a number iff every element is
--   - encoding: K depends on q, q′ and C → ∃ K > 0 chosen after C, q, q′ and before the space X; reason: quantifier form of the dependence
--   - encoding: (K, q′)-uniformly convex: R((w₁+w₂)/2) ≤ ½R(w₁)+½R(w₂) − (1/K)^{q′}‖(w₁−w₂)/2‖^{q′} → NondualOpt.IsUnifConvexOn B R ((1/(2K))^{q′}) q′; reason: (1/K)^{q′}‖(w₁−w₂)/2‖^{q′} = (1/(2K))^{q′}‖w₁−w₂‖^{q′}; same condition
--   - encoding: a (real Banach) space X, with no restriction on its size → X : Type (the lowest universe); reason: the constants are quantified before X, so X ranges over one fixed universe; universe-level convention, as in the base mission's theorem_sec2_i and theorem_3
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, unnumbered Theorem, item (ii), p.6

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_IsUnifConvexOn
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_seqRad

namespace GradSuffice.Supplement

/-- **§2 Theorem, item (ii) (Rademacher decay gives a uniformly convex regularizer).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2,
unnumbered Theorem, p.6: "Let `B` be the unit ball of a Banach space, and `B⋆` its dual unit ball.
Suppose that for some `C ≥ 1` and `q ≥ 2`, the sequential Rademacher complexity satisfies
`R⁽ˢ⁾ₘ(B) ≤ C m^{−1/q}` for every `m ≥ 1`. Then: (ii) For every `q′ > q`, there exists a continuous
convex function `R` with `0 ≤ R(w) ≤ 1` on `B`, which is `(K, q′)`-uniformly convex, where `K`
depends on `q`, `q′` and `C`."

**Formalization Note.** `K > 0` is chosen after `C, q, q′` and before the (real, complete) space.
The hypothesis is stated for every `B⋆`-valued adaptive sequence of every length `m ≥ 1` (an upper
bound on the supremum). `(K, q′)`-uniform convexity is the p.5 convention
`R((w₁+w₂)/2) ≤ ½R(w₁) + ½R(w₂) − (1/K)^{q′} ‖(w₁−w₂)/2‖^{q′}`, i.e.
`NondualOpt.IsUnifConvexOn B R ((1/(2K))^{q′}) q′`, as in the base mission. `R` is a function on
`X` of which only the values on `B` matter. -/
theorem theorem_sec2_ii :
    ∀ C q : ℝ, 1 ≤ C → 2 ≤ q → ∀ q' : ℝ, q < q' →
      ∃ K : ℝ, 0 < K ∧ ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
        (∀ m : ℕ, 1 ≤ m → ∀ ξ : NondualOpt.Tree (StrongDual ℝ X) m, IsDualValued ξ →
          seqRad ξ ≤ C * (m : ℝ) ^ (-1 / q)) →
        ∃ R : X → ℝ, ContinuousOn R (Metric.closedBall (0 : X) 1) ∧
          ConvexOn ℝ (Metric.closedBall (0 : X) 1) R ∧
          (∀ w ∈ Metric.closedBall (0 : X) 1, 0 ≤ R w ∧ R w ≤ 1) ∧
          NondualOpt.IsUnifConvexOn (Metric.closedBall (0 : X) 1) R ((1 / (2 * K)) ^ q') q' := by sorry

end GradSuffice.Supplement
