-- Prove2me | Theorems.Thm_KingmanSubadditive_Continuous_oscillation_propagates
-- name    : KingmanSubadditive.Continuous.oscillation_propagates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:44:00.075873+00:00
-- url     : https://prove2.me/theorems/26eacfdf-be91-4a0b-a16c-763fec0baabf
-- title:
--   (1.4.7) — finite oscillation propagates to bounded intervals
-- statement:
--   Let $x$ be a separable continuous-parameter subadditive process. If $E(\Omega_{[a,b]})<\infty$ for one interval with $0\le a<b$, then
--
--   $$
--   E(\Omega_J)<\infty
--   $$
--
--   for every bounded interval $J\subseteq[0,\infty)$. Thus the local integrability condition can be checked on a single nondegenerate interval and used wherever a bounded time window is needed.
--
--   **Formalization Note** An interval is an order-convex subset of the real line. Its endpoints may be included or omitted; empty and singleton intervals are allowed in the conclusion.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 889, §1.4, text after (1.4.6)–(1.4.7)

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process

namespace KingmanSubadditive.Continuous

open MeasureTheory

/-- Kingman, §1.4, after (1.4.6)–(1.4.7), p. 889. Finite expected
oscillation on one nondegenerate interval propagates to every bounded
interval of nonnegative time. Formalization Note: `Set.OrdConnected` encodes
"interval" and the probability space and separability make the expectations
of oscillations meaningful. -/
theorem oscillation_propagates {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x) (hsep : IsSeparable P x)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hosc : FiniteOscillation P x (Set.Icc a b)) :
    ∀ J : Set ℝ, Set.OrdConnected J → Bornology.IsBounded J →
      J ⊆ Set.Ici (0 : ℝ) → FiniteOscillation P x J := by sorry

end KingmanSubadditive.Continuous
