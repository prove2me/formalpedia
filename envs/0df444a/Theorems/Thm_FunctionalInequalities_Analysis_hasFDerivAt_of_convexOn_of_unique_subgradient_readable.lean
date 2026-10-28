-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_of_convexOn_of_unique_subgradient_readable
-- name    : FunctionalInequalities.Analysis.hasFDerivAt_of_convexOn_of_unique_subgradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:06.769979+00:00
-- url     : https://prove2.me/theorems/690ed838-72ba-4da4-b243-c587f4147186
-- title:
--   Differentiability From Unique Convex Subgradient
-- statement:
--   This is an auxiliary differentiability criterion for convex functions.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be convex. Fix $x,g\in E$. Assume $g$ is a subgradient at $x$:
--   $$u(x)+\langle g,y-x\rangle\le u(y)\quad\text{for all }y,$$
--   and assume it is unique: every $q$ satisfying the same supporting inequality equals $g$. Then $u$ has a Fréchet derivative at $x$, represented through the inner product by $g$:
--   $$\operatorname{HasFDerivAt}(u,\operatorname{toDual}(g),x).$$
--
--   The result is used to pass from pointwise uniqueness of subgradients to continuous differentiability.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma hasFDerivAt_of_convexOn_of_unique_subgradient {u : E → ℝ}
--       (hconv : ConvexOn ℝ Set.univ u) (x g : E)
--       (hg : ∀ y, u x + ⟪g, y - x⟫ ≤ u y)
--       (huniq : ∀ q, (∀ y, u x + ⟪q, y - x⟫ ≤ u y) → q = g) :
--       HasFDerivAt u ((InnerProductSpace.toDual ℝ E) g) x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`exists_subgradient_slope_le_inner_add`](https://prove2.me/theorems/030b4fd7-878c-4020-bf9d-be7e6b77019e).
--
--   Previous: [`ConvexOn.ae_differentiableAt_of_isOpen`](https://prove2.me/theorems/b601dd62-f116-4daf-a684-024dc3b2b841) · Next: [`support_of_max`](https://prove2.me/theorems/755fde81-3294-4941-84e6-f374b8550b71).
--
--   [Source excerpt, lines 656–660](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L656-L660) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L656-L833 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `_private.FunctionalInequalities.Analysis.Convex.Subgradient.0.FunctionalInequalities.Analysis.hasFDerivAt_of_convexOn_of_unique_subgradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma FunctionalInequalities.Analysis.hasFDerivAt_of_convexOn_of_unique_subgradient_readable {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x g : E)
    (hg : ∀ y, u x + ⟪g, y - x⟫ ≤ u y)
    (huniq : ∀ q, (∀ y, u x + ⟪q, y - x⟫ ≤ u y) → q = g) :
    HasFDerivAt u ((InnerProductSpace.toDual ℝ E) g) x := by sorry
