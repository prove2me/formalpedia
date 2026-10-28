-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_real_convexOn_legendre_readable
-- name    : FunctionalInequalities.Analysis.real_convexOn_legendre_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:33.102485+00:00
-- url     : https://prove2.me/theorems/fbb08d4f-988c-4d02-8aba-5ffd7f1a1919
-- title:
--   Convexity of a Real Legendre Representative
-- statement:
--   This transfers convexity of the extended-real Legendre epigraph to a real representative.
--
--   Let $E$ be a real inner-product space, let $q:E\to\overline{\mathbb R}$, and let $\psi:E\to\mathbb R$. Assume that for every $x\in E$,
--
--   $$
--   \operatorname{Leg}(q)(x)=\psi(x)
--   $$
--
--   where the right-hand side is coerced to `EReal`. Then $\psi$ is convex on all of $E$:
--
--   $$
--   \psi(a x+b y)\leq a\psi(x)+b\psi(y)
--   $$
--
--   whenever $a,b\geq0$ and $a+b=1$. No finite-dimensional, measurability, or bounded-domain hypothesis is required.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem real_convexOn_legendre
--       (q : E → EReal) (ψ : E → ℝ)
--       (hψ : ∀ x, legendre q x = (ψ x : EReal)) :
--       ConvexOn ℝ (univ : Set E) ψ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/BoundedConjugate`](https://prove2.me/theorems/04a83231-075b-4ff4-b344-919421d39a97).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`convex_epigraph_legendre`](https://prove2.me/theorems/ae6b66c7-c45b-4b02-ba8a-8dcdbef9e183).
--
--   Previous: [`legendre_le_of_real_lower_bound`](https://prove2.me/theorems/36c3f5d5-3ca4-4d66-abff-68d4394870f7) · Next: [`lipschitzWith_real_legendre`](https://prove2.me/theorems/a855a68c-6e7d-4b04-a93c-aa344c92d581).
--
--   [Source excerpt, lines 158–161](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L158-L161) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L155-L173 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, declaration `FunctionalInequalities.Analysis.real_convexOn_legendre`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_BoundedConjugate

open MeasureTheory Set Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.real_convexOn_legendre_readable
    (q : E → EReal) (ψ : E → ℝ)
    (hψ : ∀ x, legendre q x = (ψ x : EReal)) :
    ConvexOn ℝ (univ : Set E) ψ := by sorry
