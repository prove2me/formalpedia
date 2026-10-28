-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lowerTruncate_convexification_readable
-- name    : FunctionalInequalities.Analysis.lowerTruncate_convexification_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:45.238775+00:00
-- url     : https://prove2.me/theorems/1d40fba2-adb7-47d5-9def-9ed116ba3cc6
-- title:
--   Convexification of a Lower Truncation
-- statement:
--   This formalizes the convexification statement corresponding to Proposition 12 of Cordero–Erausquin–Klartag (arXiv:1304.0630v1).
--
--   Let $\phi:E\to\overline{\mathbb R}$ and $M\in\mathbb R$. Assume that $\phi$ has at least one point where it is not $+\infty$. Define
--
--   $$
--   g=\max(\phi,-M),\qquad c=\operatorname{Leg}(\operatorname{Leg}(g)).
--   $$
--
--   Then $c$ is a convex proper lower-semicontinuous potential, and for every $x$,
--
--   $$
--   -M\leq c(x)\leq g(x).
--   $$
--
--   Moreover, the conjugate is preserved:
--
--   $$
--   \operatorname{Leg}(c)(y)=\operatorname{Leg}(g)(y)
--   $$
--
--   for every $y$. The construction requires no convexity assumption on the original $\phi$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lowerTruncate_convexification (φ : E → EReal) (M : ℝ)
--       (hfinite : ∃ x, φ x ≠ ⊤) :
--       let g := lowerTruncate φ M
--       let c := legendre (legendre g)
--       ConvexPotential c ∧ LowerSemicontinuous c ∧ ProperPotential c ∧
--         (∀ x, ((-M : ℝ) : EReal) ≤ c x ∧ c x ≤ g x) ∧
--         (∀ y, legendre c y = legendre g y)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`convex_epigraph_legendre`](https://prove2.me/theorems/ae6b66c7-c45b-4b02-ba8a-8dcdbef9e183), [`legendre_ne_bot_iff`](https://prove2.me/theorems/9d709974-65b3-421f-a939-a9573b181df1).
--
--   Previous: [`legendre_ne_bot_iff`](https://prove2.me/theorems/9d709974-65b3-421f-a939-a9573b181df1) · Next: [`legendre_eq_interior_sup`](https://prove2.me/theorems/fb27a67d-8a39-4dbc-904c-e8977c7bb3af).
--
--   [Source excerpt, lines 228–234](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L228-L234) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L225-L245 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.lowerTruncate_convexification`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.lowerTruncate_convexification_readable (φ : E → EReal) (M : ℝ)
    (hfinite : ∃ x, φ x ≠ ⊤) :
    let g := lowerTruncate φ M
    let c := legendre (legendre g)
    ConvexPotential c ∧ LowerSemicontinuous c ∧ ProperPotential c ∧
      (∀ x, ((-M : ℝ) : EReal) ≤ c x ∧ c x ≤ g x) ∧
      (∀ y, legendre c y = legendre g y) := by sorry
