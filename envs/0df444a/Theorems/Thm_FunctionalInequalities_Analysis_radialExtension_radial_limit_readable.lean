-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_radialExtension_radial_limit_readable
-- name    : FunctionalInequalities.Analysis.radialExtension_radial_limit_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:14.483646+00:00
-- url     : https://prove2.me/theorems/bbb9246f-b710-4e74-a805-3997176540ae
-- title:
--   Radial Extension Has Its Radial Limit
-- statement:
--   This auxiliary lemma establishes radial continuity of a convex radial extension.
--
--   Let $E$ be finite-dimensional over $\mathbb R$, let $K\subseteq E$ be open with $0\in K$, and let $g:E\to\mathbb R$ be convex on $K$. Assume:
--
--   1. $g(x)\ge0$ for every $x\in K$.
--   2. $g(0)=0$.
--
--   For every $x\in E$, the radial extension `radialExtension K g` satisfies
--   $$\operatorname{radialExtension}(K,g)(tx)\longrightarrow\operatorname{radialExtension}(K,g)(x)$$
--   as $t\to1$ from below.
--
--   This is an internal continuity property used in constructing extended-real convex limits.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma radialExtension_radial_limit {K : Set E} (hK : IsOpen K) (h0K : (0 : E) ∈ K)
--       {g : E → ℝ} (hg : ConvexOn ℝ K g) (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0) (x : E) :
--       Tendsto (fun t : ℝ => radialExtension K g (t • x)) (nhdsWithin 1 (Set.Iio 1))
--         (nhds (radialExtension K g x))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/RadialExtension`](https://prove2.me/theorems/da2489dd-75ed-4659-a13a-f2ad3f5ccb75).
--
--   [Source excerpt, lines 208–211](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/RadialExtension.lean#L208-L211) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/RadialExtension.lean#L208-L262 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.RadialExtension`, declaration `_private.FunctionalInequalities.Analysis.Convex.RadialExtension.0.FunctionalInequalities.Analysis.radialExtension_radial_limit`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_RadialExtension

open Set Filter
variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma FunctionalInequalities.Analysis.radialExtension_radial_limit_readable {K : Set E} (hK : IsOpen K) (h0K : (0 : E) ∈ K)
    {g : E → ℝ} (hg : ConvexOn ℝ K g) (hnn : ∀ x ∈ K, 0 ≤ g x) (hg0 : g 0 = 0) (x : E) :
    Tendsto (fun t : ℝ => FunctionalInequalities.Analysis.radialExtension K g (t • x)) (nhdsWithin 1 (Set.Iio 1))
      (nhds (FunctionalInequalities.Analysis.radialExtension K g x)) := by sorry
