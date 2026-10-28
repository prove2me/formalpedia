-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_ne_bot_iff_readable
-- name    : FunctionalInequalities.Analysis.legendre_ne_bot_iff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:44.45897+00:00
-- url     : https://prove2.me/theorems/9d709974-65b3-421f-a939-a9573b181df1
-- title:
--   Characterization of Finite-Above Legendre Values
-- statement:
--   This characterizes when a Legendre transform value is not negative infinity.
--
--   Let $\phi:E\to\overline{\mathbb R}$ and $y\in E$. Then
--
--   $$
--   \operatorname{Leg}(\phi)(y)\neq-\infty
--   \quad\Longleftrightarrow\quad
--   \exists x\in E,\ \phi(x)\neq+\infty.
--   $$
--
--   Thus the conjugate avoids $-\infty$ exactly when the effective domain of $\phi$ is nonempty. No convexity, measurability, or finiteness assumptions are imposed on the input.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem legendre_ne_bot_iff (φ : E → EReal) (y : E) :
--       legendre φ y ≠ ⊥ ↔ ∃ x, φ x ≠ ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Previous: [`convex_epigraph_legendre`](https://prove2.me/theorems/ae6b66c7-c45b-4b02-ba8a-8dcdbef9e183) · Next: [`lowerTruncate_convexification`](https://prove2.me/theorems/1d40fba2-adb7-47d5-9def-9ed116ba3cc6).
--
--   [Source excerpt, lines 182–183](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L182-L183) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L180-L204 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.legendre_ne_bot_iff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.legendre_ne_bot_iff_readable (φ : E → EReal) (y : E) :
    legendre φ y ≠ ⊥ ↔ ∃ x, φ x ≠ ⊤ := by sorry
