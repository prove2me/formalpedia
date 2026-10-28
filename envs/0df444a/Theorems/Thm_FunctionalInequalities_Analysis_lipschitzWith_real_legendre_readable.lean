-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_real_legendre_readable
-- name    : FunctionalInequalities.Analysis.lipschitzWith_real_legendre_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:32.875032+00:00
-- url     : https://prove2.me/theorems/a855a68c-6e7d-4b04-a93c-aa344c92d581
-- title:
--   Lipschitz Representative of a Finite Legendre Transform
-- statement:
--   This shows that bounded effective-domain slopes yield a Lipschitz real representative of the Legendre transform.
--
--   Let $E$ be a real inner-product space, let $q:E\to\overline{\mathbb R}$, let $L\in[0,\infty)$, and let $\psi:E\to\mathbb R$. Assume:
--
--   1. $q(y)\neq-\infty$ for every $y$;
--   2. whenever $q(y)\neq+\infty$, one has $y\in\overline B(0,L)$;
--   3. $\operatorname{Leg}(q)(x)=\psi(x)$ as an extended-real equality for every $x$.
--
--   Then `ψ` is $L$-Lipschitz, expressed by `LipschitzWith L ψ`.
--
--   Only finite values of $q$ are converted using `toReal`; the supremum itself remains an extended-real supremum.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lipschitzWith_real_legendre
--       (q : E → EReal) (L : NNReal) (ψ : E → ℝ)
--       (hbot : ∀ y, q y ≠ ⊥)
--       (hdom : ∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
--       (hψ : ∀ x, legendre q x = (ψ x : EReal)) :
--       LipschitzWith L ψ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/BoundedConjugate`](https://prove2.me/theorems/04a83231-075b-4ff4-b344-919421d39a97).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Previous: [`real_convexOn_legendre`](https://prove2.me/theorems/fbb08d4f-988c-4d02-8aba-5ffd7f1a1919).
--
--   [Source excerpt, lines 178–183](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L178-L183) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L175-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.lipschitzWith_real_legendre`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate

open MeasureTheory Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.lipschitzWith_real_legendre_readable
    (q : E → EReal) (L : NNReal) (ψ : E → ℝ)
    (hbot : ∀ y, q y ≠ ⊥)
    (hdom : ∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ))
    (hψ : ∀ x, legendre q x = (ψ x : EReal)) :
    LipschitzWith L ψ := by sorry
