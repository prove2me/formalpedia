-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Deterministic_lemma_4_1
-- name    : NearlyUnstableHawkes.Deterministic.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:35.818426+00:00
-- url     : https://prove2.me/theorems/6e5f6b43-16d5-4ade-98f2-95c68eff8edd
-- title:
--   Lemma 4.1, p. 15 — renewal equation resolved by ψᵀ
-- statement:
--   Let $\phi^T=a\phi$ with $0<a<1$ and $\phi$ satisfying Assumption 1. Suppose measurable functions $f,h$ are bounded on each compact subinterval of $[0,\infty)$ and satisfy, for every $t\ge0$,
--
--   $$f(t)=h(t)+\int_0^t\phi^T(t-s)f(s)\,ds.$$
--
--   Then the **resolvent** $\psi^T=\sum_{k\ge1}(\phi^T)^{*k}$ gives
--
--   $$f(t)=h(t)+\int_0^t\psi^T(t-s)h(s)\,ds\qquad(t\ge0).$$
--
--   This is the renewal identity used to express the Hawkes mean and centered process.
--
--   **Formalization Note** Local boundedness and measurability of $f$ are explicit so the renewal integral has its intended value. The paper names these properties only for $h$.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 15, Lemma 4.1

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

namespace NearlyUnstableHawkes.Deterministic

open MeasureTheory

/-- Jaisson–Rosenbaum, Lemma 4.1, p. 15. -/
theorem lemma_4_1 (a m : ℝ) (φ φ' f h : ℝ → ℝ)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : KernelAssumption φ φ' m)
    (hfmeas : Measurable f) (hhmeas : Measurable h)
    (hfloc : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) R, |f t| ≤ C)
    (hhloc : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) R, |h t| ≤ C)
    (heq : ∀ t : ℝ, 0 ≤ t →
      f t = h t + conv (scaledKernel a φ) f t) :
    ∀ t : ℝ, 0 ≤ t →
      f t = h t + conv (psi (scaledKernel a φ)) h t := by sorry

end NearlyUnstableHawkes.Deterministic
