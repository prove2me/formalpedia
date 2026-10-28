-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradient_expansion_of_hasFDerivAt_resolvent_readable
-- name    : FunctionalInequalities.Analysis.subgradient_expansion_of_hasFDerivAt_resolvent_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:24.114512+00:00
-- url     : https://prove2.me/theorems/87eddc48-68f3-46a2-9e7f-49882aba3799
-- title:
--   Subgradient Expansion at an Invertibly Differentiable Resolvent
-- statement:
--   This is an auxiliary local inverse-resolvent statement for convex subgradients.
--
--   Let $E$ be a real inner-product space, let $f:E\to\mathbb R$ and $P:E\to E$, and assume
--
--   $$f(Pz)+\langle z-Pz,y-Pz\rangle\le f(y)\qquad(z,y\in E).$$
--
--   Fix $z\in E$ and let $T:E\to E$ be a continuous linear equivalence such that $P$ is Fréchet differentiable at $z$ with derivative $T$. Then:
--
--   1. The only subgradient of $f$ at $Pz$ is $z-Pz$.
--   2. For every $\varepsilon>0$, for all $y$ sufficiently near $Pz$, every subgradient $q$ of $f$ at $y$ satisfies
--      $$\left\|q-(z-Pz)-\left(T^{-1}(y-Pz)-(y-Pz)\right)\right\|\le \varepsilon\|y-Pz\|.$$
--
--   The declaration `subgradient_expansion_of_hasFDerivAt_resolvent_readable` is a local quantitative description of the subdifferential near the image point of an invertibly differentiable resolvent.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem subgradient_expansion_of_hasFDerivAt_resolvent {f : E → ℝ} {P : E → E}
--       (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E} {T : E ≃L[ℝ] E}
--       (hT : HasFDerivAt P (T : E →L[ℝ] E) z) :
--       (∀ q : E, (∀ y, f (P z) + ⟪q, y - P z⟫ ≤ f y) → q = z - P z) ∧
--       ∀ ε > 0, ∀ᶠ y in 𝓝 (P z), ∀ q : E, (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
--         ‖q - (z - P z) - (T.symm (y - P z) - (y - P z))‖ ≤ ε * ‖y - P z‖
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SecondOrder`](https://prove2.me/theorems/25ef7ab1-0f22-4192-9c58-d196bc21f161).
--
--   Supporting theorems: [`resolvent_preimage_near`](https://prove2.me/theorems/253f1fd8-dbe8-46e5-8918-38675b5d625a).
--
--   Previous: [`resolvent_preimage_near`](https://prove2.me/theorems/253f1fd8-dbe8-46e5-8918-38675b5d625a) · Next: [`tendsto_integral_secondDifference_mul`](https://prove2.me/theorems/4354b6fd-00d6-4dd4-9dfb-0b7b24838470).
--
--   [Source excerpt, lines 153–158](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L153-L158) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean#L147-L246 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondOrder`, declaration `FunctionalInequalities.Analysis.subgradient_expansion_of_hasFDerivAt_resolvent`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder

open scoped RealInnerProductSpace Topology
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.subgradient_expansion_of_hasFDerivAt_resolvent_readable {f : E → ℝ} {P : E → E}
    (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E} {T : E ≃L[ℝ] E}
    (hT : HasFDerivAt P (T : E →L[ℝ] E) z) :
    (∀ q : E, (∀ y, f (P z) + ⟪q, y - P z⟫ ≤ f y) → q = z - P z) ∧
    ∀ ε > 0, ∀ᶠ y in 𝓝 (P z), ∀ q : E, (∀ w, f y + ⟪q, w - y⟫ ≤ f w) →
      ‖q - (z - P z) - (T.symm (y - P z) - (y - P z))‖ ≤ ε * ‖y - P z‖ := by sorry
