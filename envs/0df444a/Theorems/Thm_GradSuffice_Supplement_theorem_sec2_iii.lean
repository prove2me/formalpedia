-- Prove2me | Theorems.Thm_GradSuffice_Supplement_theorem_sec2_iii
-- name    : GradSuffice.Supplement.theorem_sec2_iii
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:28:08.315462+00:00
-- url     : https://prove2.me/theorems/de5285aa-d324-4e09-8cc1-f72eabbbb3c4
-- title:
--   §2 Theorem (iii), p.6 — $\mathcal R^{(s)}_m(B)\le Cm^{-1/q}$ gives iteration complexity $O_{q,q'}((C/\varepsilon)^{q'})$ for every $q'>q$
-- statement:
--   Let $B$ be the unit ball of a real Banach space $X$. Suppose that for some $C\ge1$ and $q\ge2$ the sequential Rademacher complexity satisfies $\mathcal R^{(s)}_m(B)\le C\,m^{-1/q}$ for every $m\ge1$. Then, for every $q'>q$, Mirror Descent with an appropriate regularizer achieves iteration complexity
--   $$T(\varepsilon)=O_{q,q'}\big((C/\varepsilon)^{q'}\big).$$
--   Precisely: there is a constant $A>0$ depending only on $q$ and $q'$ such that for every $0<\varepsilon\le1$ some deterministic first-order algorithm making $T\le A\,(C/\varepsilon)^{q'}$ queries over $B$ outputs a point $w_T$ with
--   $$f(w_T)-\inf_{w\in B}f(w)\le\varepsilon$$
--   for every convex 1-Lipschitz objective $f$ (defined on an open convex neighbourhood of $B$) and every valid first-order oracle.
--
--   This is the classical upper bound that Theorem 2 complements with a lower bound in terms of the same quantity.
--
--   **Formalization Note** The algorithm's output is its last query, as in the paper's model; the query count includes it. The hypothesis bounds $\mathcal R^{(s)}_m(B;\bar\xi)$ for every $B^\star$-valued adaptive sequence.
--
--   Differences from the source:
--   - encoding: R⁽ˢ⁾ₘ(B) ≤ C m^{−1/q} (a supremum over adaptive sequences) → seqRad ξ ≤ C m^{−1/q} for every B⋆-valued adaptive sequence ξ of every length m ≥ 1; reason: a supremum is at most a number iff every element is
--   - reading: T(ε) = O_{q,q′}((C/ε)^{q′}) → ∃ A > 0 depending only on q, q′ (chosen before C and X) with T ≤ A (C/ε)^{q′} for every 0 < ε ≤ 1; reason: O-notation as ε → 0 with the hidden constant depending only on the subscripts; C stays explicit; for large ε no positive query count is below A(C/ε)^{q′}, so the bound is asymptotic
--   - reading: Mirror Descent with the appropriate regularizer achieves → there exists a deterministic DetAlg over B with T queries whose last query is ε-accurate for every objective and every valid oracle; reason: iteration complexity is a statement about the existence of an algorithm; Mirror Descent is deterministic and its output is queried once more (p.4), as in the base Eq. (2) milestone
--   - encoding: a (real Banach) space X, with no restriction on its size → X : Type (the lowest universe); reason: the constants are quantified before X, so X ranges over one fixed universe; universe-level convention, as in the base mission's theorem_sec2_i and theorem_3
--   - reading: every valid first-order oracle ("O receives a point w ∈ W and returns a pair (f(w), ξ)") → every fixed subgradient selection w ↦ g(w) (IsValidOracle F g); reason: p.4 defines the oracle as a map from the queried point to the answer; as in the base mission's Eq. (2) milestone
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, unnumbered Theorem, item (iii), Eq. (5), p.6 (restated §3.3, p.9)

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_seqRad
import Definitions.Def_GradSuffice_IsValidOracle
import Definitions.Def_GradSuffice_DetAlg_lastQuery

namespace GradSuffice.Supplement

/-- **§2 Theorem, item (iii) (Mirror Descent rate from Rademacher decay).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, unnumbered
Theorem, p.6: "Suppose that for some `C ≥ 1` and `q ≥ 2`, the sequential Rademacher complexity
satisfies `R⁽ˢ⁾ₘ(B) ≤ C m^{−1/q}` for every `m ≥ 1`. Then: […] (iii) Mirror Descent with the
appropriate regularizer achieves iteration complexity `T(ε) = O_{q,q′}((C/ε)^{q′})` for every
`q′ > q`." (Eq. (5); restated in §3.3, p.9.)

**Formalization Note.** The `O_{q,q′}` constant is an `A > 0` depending only on `q` and `q′`,
chosen before `C` and before the space; `C` appears explicitly in the bound. "Mirror Descent
achieves iteration complexity `T(ε)`" is encoded as in the base mission's Eq. (2) milestone: for
every `0 < ε ≤ 1` there is a deterministic algorithm with `T ≤ A (C/ε)^{q′}` queries (the output is
the last query) whose output is within `ε` of `inf_B f` for every objective and every valid oracle.
The `O(·)` is read as `ε → 0` (`ε ≤ 1`). -/
theorem theorem_sec2_iii :
    ∀ q : ℝ, 2 ≤ q → ∀ q' : ℝ, q < q' → ∃ A : ℝ, 0 < A ∧
      ∀ C : ℝ, 1 ≤ C → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
        (∀ m : ℕ, 1 ≤ m → ∀ ξ : NondualOpt.Tree (StrongDual ℝ X) m, IsDualValued ξ →
          seqRad ξ ≤ C * (m : ℝ) ^ (-1 / q)) →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∃ T : ℕ, 0 < T ∧ (T : ℝ) ≤ A * (C / ε) ^ q' ∧
            ∃ alg : DetAlg X (Metric.closedBall (0 : X) 1) T,
              ∀ (F : Objective X (Metric.closedBall (0 : X) 1)) (g : X → StrongDual ℝ X),
                IsValidOracle F g →
                F.f (alg.lastQuery F.f g) - sInf (F.f '' Metric.closedBall (0 : X) 1) ≤ ε := by sorry

end GradSuffice.Supplement
