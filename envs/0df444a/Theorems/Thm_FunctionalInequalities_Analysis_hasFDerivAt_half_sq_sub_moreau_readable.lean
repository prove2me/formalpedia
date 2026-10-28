-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_half_sq_sub_moreau_readable
-- name    : FunctionalInequalities.Analysis.hasFDerivAt_half_sq_sub_moreau_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:15.638728+00:00
-- url     : https://prove2.me/theorems/746705d4-4726-407e-8f1b-f9fdde75a858
-- title:
--   Derivative of the Quadratic Minus Moreau Expression
-- statement:
--   This is an auxiliary differentiability statement for a resolvent-type map.
--
--   Let $E$ be a real inner-product space, let $f:E\to\mathbb R$ and $P:E\to E$, and assume that for all $z,y\in E$,
--
--   $$f(Pz)+\langle z-Pz,y-Pz\rangle\le f(y).$$
--
--   Then, at every $z\in E$, the function
--
--   $$w\longmapsto \frac12\|w\|^2-\left(f(Pw)+\frac12\|Pw-w\|^2\right)$$
--
--   has Fréchet derivative represented by the inner product with $Pz$:
--
--   $$D\!\left[\frac12\|\cdot\|^2-f(P\cdot)-\frac12\|P\cdot-\cdot\|^2\right]_z(v)=\langle Pz,v\rangle.$$
--
--   In Lean this derivative is expressed as `HasFDerivAt` with linear map `innerSL ℝ (P z)`. The result requires no convexity hypothesis beyond the displayed subgradient inequality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasFDerivAt_half_sq_sub_moreau
--       {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) (z : E) :
--       HasFDerivAt (fun w => (1 / 2) * ‖w‖ ^ 2 - (f (P w) + (1 / 2) * ‖P w - w‖ ^ 2))
--         (innerSL ℝ (P z)) z
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Proximal`](https://prove2.me/theorems/1d665bc1-5792-4d08-9238-1bf12adef58c).
--
--   Previous: [`lipschitzWith_proximalPoint`](https://prove2.me/theorems/400fd9e1-fb0c-4e87-8ab5-d48890ee12a0) · Next: [`inner_hasFDerivAt_resolvent_symm`](https://prove2.me/theorems/403fd5b6-c99c-485d-b4de-1d3af30e51e9).
--
--   [Source excerpt, lines 204–207](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L204-L207) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L202-L239 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Proximal`, declaration `FunctionalInequalities.Analysis.hasFDerivAt_half_sq_sub_moreau`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Proximal

open scoped RealInnerProductSpace Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.hasFDerivAt_half_sq_sub_moreau_readable
    {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) (z : E) :
    HasFDerivAt (fun w => (1 / 2) * ‖w‖ ^ 2 - (f (P w) + (1 / 2) * ‖P w - w‖ ^ 2))
      (innerSL ℝ (P z)) z := by sorry
