-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_real_global_minimum_of_bounded_domain_readable
-- name    : FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:22.758513+00:00
-- url     : https://prove2.me/theorems/7afbf80a-1864-49d4-8e93-ff4674a5643f
-- title:
--   Finite Real Minimum on a Bounded Effective Domain
-- statement:
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$, and let $L\in[0,\infty)$. Assume $\phi(y)\ne-\infty$ for every $y$, some value of $\phi$ is finite, $\phi$ is lower semicontinuous, and every point where $\phi(y)\ne+\infty$ lies in the closed ball $\overline B(0,L)$. Then there exist $a\in\overline B(0,L)$ and $m\in\mathbb R$ such that
--
--   $$\phi(a)=m\quad\text{and}\quad m\le\phi(y)\ \text{for every }y\in E.$$
--
--   The conclusion explicitly produces a real-valued global minimum after excluding both extended-real infinities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_real_global_minimum_of_bounded_domain
--       (φ : E → EReal) (L : NNReal)
--       (hbot : ∀ y, φ y ≠ ⊥)
--       (hfinite : ∃ y, φ y ≠ ⊤)
--       (hlsc : LowerSemicontinuous φ)
--       (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) :
--       ∃ a ∈ closedBall (0 : E) (L : ℝ), ∃ m : ℝ,
--         φ a = (m : EReal) ∧ ∀ y, (m : EReal) ≤ φ y
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/BoundedConjugate`](https://prove2.me/theorems/04a83231-075b-4ff4-b344-919421d39a97).
--
--   Previous: [`closedBallCap_lowerSemicontinuous`](https://prove2.me/theorems/de51ab97-7601-407d-8eec-11705d7f5fe2) · Next: [`legendre_le_of_real_lower_bound`](https://prove2.me/theorems/36c3f5d5-3ca4-4d66-abff-68d4394870f7).
--
--   [Source excerpt, lines 72–79](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L72-L79) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L69-L102 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate

open MeasureTheory Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain_readable
    (φ : E → EReal) (L : NNReal)
    (hbot : ∀ y, φ y ≠ ⊥)
    (hfinite : ∃ y, φ y ≠ ⊤)
    (hlsc : LowerSemicontinuous φ)
    (hdom : ∀ y, φ y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) :
    ∃ a ∈ closedBall (0 : E) (L : ℝ), ∃ m : ℝ,
      φ a = (m : EReal) ∧ ∀ y, (m : EReal) ≤ φ y := by sorry
