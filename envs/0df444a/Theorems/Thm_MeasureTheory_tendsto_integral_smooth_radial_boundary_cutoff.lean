-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_integral_smooth_radial_boundary_cutoff
-- name    : MeasureTheory.tendsto_integral_smooth_radial_boundary_cutoff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T10:22:33.433207+00:00
-- url     : https://prove2.me/theorems/fc270614-31ae-4a49-be15-cf6ca9070fb1
-- title:
--   Derivatives of smooth radial cutoffs concentrate at the boundary
-- statement:
--   Let $r>0$, let $H:\mathbb R\to\mathbb R$ be continuous on $[0,r]$, and let $0<\varepsilon_k\le r^2$ tend to zero. Write $\theta$ for Mathlib's smooth increasing transition from zero to one on $[0,1]$, and set $q_k(t)=\theta((r^2-t^2)/\varepsilon_k)$. Then
--
--   $$\lim_{k\to\infty}\int_0^r -q_k'(t)H(t)\,dt=H(r).$$
--
--   This boundary approximate identity turns a radial shell integral into evaluation at the outer radius.
-- source:
--   Elementary approximate-identity lemma developed for the ball specialization of Hunter, Notes on PDEs, Theorem 1.46, printed p. 17, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. Uses the fundamental theorem of calculus and continuity on [0,r].

import Definitions.Def_HunterPDE_Harmonic_MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory MeasureTheory.Measure Set Metric Filter Function
open scoped Topology
set_option autoImplicit false

theorem MeasureTheory.tendsto_integral_smooth_radial_boundary_cutoff {r : ℝ} (hr : 0 < r) {H : ℝ → ℝ} (hH : ContinuousOn H (Icc 0 r))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hεr : ∀ k, ε k ≤ r ^ 2)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t in 0..r,
      -deriv (fun s : ℝ => Real.smoothTransition ((r ^ 2 - s ^ 2) / ε k)) t * H t)
      atTop (𝓝 (H r)) := by sorry
