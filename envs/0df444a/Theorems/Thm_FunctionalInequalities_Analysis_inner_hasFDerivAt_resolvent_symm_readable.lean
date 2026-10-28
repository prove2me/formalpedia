-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inner_hasFDerivAt_resolvent_symm_readable
-- name    : FunctionalInequalities.Analysis.inner_hasFDerivAt_resolvent_symm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:16.889545+00:00
-- url     : https://prove2.me/theorems/403fd5b6-c99c-485d-b4de-1d3af30e51e9
-- title:
--   Symmetry and Firm Nonexpansiveness of the Resolvent Derivative
-- statement:
--   This statement records structural properties of a differentiable resolvent.
--
--   Let $E$ be a real inner-product space, let $f:E\to\mathbb R$ and $P:E\to E$, and assume
--
--   $$f(Pz)+\langle z-Pz,y-Pz\rangle\le f(y)\qquad(z,y\in E).$$
--
--   Fix $z\in E$ and suppose that $P$ has Fréchet derivative $T:E\to E$ at $z$. Then, for every $v,w\in E$,
--
--   $$\langle Tv,w\rangle=\langle v,Tw\rangle,
--   \qquad \|Tv\|^2\le \langle Tv,v\rangle.$$
--
--   The declaration `inner_hasFDerivAt_resolvent_symm_readable` provides symmetry and the firmly nonexpansive quadratic inequality for the derivative at a single point. It is a local linear-algebraic property and does not assert global differentiability of $P$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_hasFDerivAt_resolvent_symm
--       {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E}
--       {T : E →L[ℝ] E} (hT : HasFDerivAt P T z) (v w : E) :
--       ⟪T v, w⟫ = ⟪v, T w⟫ ∧ ‖T v‖ ^ 2 ≤ ⟪T v, v⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Proximal`](https://prove2.me/theorems/1d665bc1-5792-4d08-9238-1bf12adef58c).
--
--   Supporting theorems: [`hasFDerivAt_half_sq_sub_moreau`](https://prove2.me/theorems/746705d4-4726-407e-8f1b-f9fdde75a858).
--
--   Previous: [`hasFDerivAt_half_sq_sub_moreau`](https://prove2.me/theorems/746705d4-4726-407e-8f1b-f9fdde75a858).
--
--   [Source excerpt, lines 244–247](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L244-L247) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L241-L288 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Proximal`, declaration `FunctionalInequalities.Analysis.inner_hasFDerivAt_resolvent_symm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Proximal

open scoped RealInnerProductSpace Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.inner_hasFDerivAt_resolvent_symm_readable
    {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E}
    {T : E →L[ℝ] E} (hT : HasFDerivAt P T z) (v w : E) :
    ⟪T v, w⟫ = ⟪v, T w⟫ ∧ ‖T v‖ ^ 2 ≤ ⟪T v, v⟫ := by sorry
