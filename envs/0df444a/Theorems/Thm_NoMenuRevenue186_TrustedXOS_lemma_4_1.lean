-- Prove2me | Theorems.Thm_NoMenuRevenue186_TrustedXOS_lemma_4_1
-- name    : NoMenuRevenue186.TrustedXOS.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:57.731477+00:00
-- url     : https://prove2.me/theorems/631f1002-de25-4bfa-8834-973c0314fe95
-- title:
--   Lemma 4.1 — almost-disjoint exact-size bundle family
-- statement:
--   There is a universal constant $\gamma>0$ such that, for every item count $n$, bundle size $k$, and overlap fraction $\epsilon$ satisfying $0<\epsilon<1$, $\epsilon k\ge2$, and $k\le\epsilon n/8$, there is a family $\mathcal F$ of subsets of the $n$ items with
--
--   $$|\mathcal F|\ge\exp(\gamma\epsilon k),\qquad
--   |S|=k\ (S\in\mathcal F),\qquad
--   |S\cap T|\le\epsilon k\ (S\ne T,\ S,T\in\mathcal F).$$
--
--   This family supplies the candidate bundles of the hard auction instance. The constant is independent of all three parameters.
--
--   Differences from the source:
--   - encoding: subsets of [n] → finite subsets of Fin n; reason: the order-preserving relabeling changes no subset, cardinality, or intersection bound
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.14, PDF p.16, Lemma 4.1

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Construction

namespace NoMenuRevenue186.TrustedXOS

/-- Lemma 4.1, printed p.14 (PDF p.16). The positive exponent constant
    is chosen before every instance parameter. -/
theorem lemma_4_1 :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (n k : ℕ) (ε : ℝ),
      0 < ε → ε < 1 → 2 ≤ ε * (k : ℝ) → (k : ℝ) ≤ ε * (n : ℝ) / 8 →
      ∃ F : Finset (Bundle n),
        Real.exp (γ * ε * (k : ℝ)) ≤ (F.card : ℝ) ∧ Separated F k ε := by sorry

end NoMenuRevenue186.TrustedXOS
