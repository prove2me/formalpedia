-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_closedBallCap_lowerSemicontinuous_readable
-- name    : FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:27.935186+00:00
-- url     : https://prove2.me/theorems/de51ab97-7601-407d-8eec-11705d7f5fe2
-- title:
--   Lower Semicontinuity After Closed-Ball Capping
-- statement:
--   This proves preservation of lower semicontinuity under the closed-ball cap operation.
--
--   Let $E$ be a normed additive commutative group, let $\varphi:E\to[-\infty,\infty]$ be extended-real valued, and let $L\in[0,\infty)$. If $\varphi$ is lower semicontinuous, then `closedBallCap φ L` is lower semicontinuous:
--
--   $$
--   \operatorname{LSC}(\varphi)\Longrightarrow\operatorname{LSC}(\operatorname{closedBallCap}(\varphi,L)).
--   $$
--
--   The operation agrees with $\varphi$ on the closed ball of radius $L$ centered at $0$ and takes the value $+\infty$ outside it. The declaration is `closedBallCap_lowerSemicontinuous_readable`; no inner-product, finite-dimensional, or measurable-space assumptions are present in the statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem closedBallCap_lowerSemicontinuous
--    (φ : E → EReal) (L : NNReal)
--       (hφ : LowerSemicontinuous φ) : LowerSemicontinuous (closedBallCap φ L)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/BoundedConjugate`](https://prove2.me/theorems/04a83231-075b-4ff4-b344-919421d39a97).
--
--   Next: [`exists_real_global_minimum_of_bounded_domain`](https://prove2.me/theorems/7afbf80a-1864-49d4-8e93-ff4674a5643f).
--
--   [Source excerpt, lines 43–45](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L43-L45) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L40-L67 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous_readable
 (φ : E → EReal) (L : NNReal)
    (hφ : LowerSemicontinuous φ) : LowerSemicontinuous (closedBallCap φ L) := by sorry
