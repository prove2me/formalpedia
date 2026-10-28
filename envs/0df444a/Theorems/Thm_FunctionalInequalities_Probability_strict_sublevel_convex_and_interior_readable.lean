-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_strict_sublevel_convex_and_interior_readable
-- name    : FunctionalInequalities.Probability.strict_sublevel_convex_and_interior_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:46.98297+00:00
-- url     : https://prove2.me/theorems/463b9839-1217-4882-805b-3a7aca81934e
-- title:
--   Convexity And Interior Of A Strict Sublevel Set
-- statement:
--   This auxiliary lemma concerns strict sublevel geometry for an extended-real convex function.
--
--   Let $E$ be finite-dimensional with a real inner product, and let $\phi:E\to\overline{\mathbb R}$. Assume:
--
--   1. $\phi(x)\ge0$ for every $x$.
--   2. The real epigraph of $\phi$ is convex.
--   3. $x_0$ lies in the interior of $\{x:\phi(x)\ne+\infty\}$.
--   4. $\phi(y)<\phi(x_0)$.
--
--   Then the strict sublevel set
--   $$\{x:\phi(x)<\phi(x_0)\}$$
--   is convex and has nonempty interior.
--
--   The result is an internal geometric component for pointwise control of convex extended-real functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma strict_sublevel_convex_and_interior {φ : E → EReal}
--       (h0 : ∀ x, 0 ≤ φ x) (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)})
--       {x₀ y : E} (hx₀ : x₀ ∈ interior {x | φ x ≠ ⊤}) (hy : φ y < φ x₀) :
--       Convex ℝ {x | φ x < φ x₀} ∧ (interior {x | φ x < φ x₀}).Nonempty
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e).
--
--   Supporting theorems: [`real_convexOn_effective_domain`](https://prove2.me/theorems/f7c7760e-e128-40c5-a6ce-efaac3655fcc).
--
--   Previous: [`real_convexOn_effective_domain`](https://prove2.me/theorems/f7c7760e-e128-40c5-a6ce-efaac3655fcc) · Next: [`exists_pos_le_mul_lintegral_toReal_of_convex_epigraph`](https://prove2.me/theorems/47effa70-14be-45e1-bd3e-85ca90620000).
--
--   [Source excerpt, lines 565–568](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L565-L568) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/ConvexSupport.lean#L565-L611 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.ConvexSupport`, declaration `_private.FunctionalInequalities.Probability.ConvexSupport.0.FunctionalInequalities.Probability.strict_sublevel_convex_and_interior`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma FunctionalInequalities.Probability.strict_sublevel_convex_and_interior_readable {φ : E → EReal}
    (h0 : ∀ x, 0 ≤ φ x) (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)})
    {x₀ y : E} (hx₀ : x₀ ∈ interior {x | φ x ≠ ⊤}) (hy : φ y < φ x₀) :
    Convex ℝ {x | φ x < φ x₀} ∧ (interior {x | φ x < φ x₀}).Nonempty := by sorry
