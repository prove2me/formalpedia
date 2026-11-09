-- Prove2me | Theorems.Thm_FourBlockIP350_Main_coarse_convex_extension
-- name    : FourBlockIP350.Main.coarse_convex_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:26.300127+00:00
-- url     : https://prove2.me/theorems/8ded73a8-b616-4689-b9f5-7432c91cc3d2
-- title:
--   Lemma 4.2 — Finite midpoint-convex functions on a coarser lattice
-- statement:
--   For $k\ge1$ and every everywhere finite midpoint-convex function $h:\mathbb Z^k\to\mathbb R$, every integer translate has a convex extension after dilation by $k$:
--   $$v\longmapsto h(\tau+kv),\qquad\tau\in\mathbb Z^k.$$
--   The extension is a finite real-valued convex function on all of $\mathbb R^k$, agreeing at every integer argument. The hypothesis tests only pairs with an integral midpoint, with no floor/ceiling condition for other pairs.
--
--   This is the complete infinite-lattice statement needed for the optimization period.
--
--   Differences from the source: none.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 10, Lemma 4.2

import Mathlib
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

namespace FourBlockIP350.Main

open scoped BigOperators

theorem coarse_convex_extension {k : ℕ} (hk : 0 < k) (h : ZVec k → ℝ)
    (hh : MidpointConvex h) (τ : ZVec k) :
    ConvexExtensible (fun v => h (τ + (k : ℤ) • v)) := by sorry

end FourBlockIP350.Main
