-- Prove2me | Theorems.Thm_MasulloRepair_pole_cell_overlap
-- name    : MasulloRepair.pole_cell_overlap
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T19:31:16.134147+00:00
-- url     : https://prove2.me/theorems/01222299-51e8-42cb-82b6-2c24df6ddd21
-- title:
--   Explicit pole-cell overlaps and their compensating geometric sum
-- statement:
--   Fix $L>0$. For $k\ge0$ let the profile on the $k$th cell be
--   $$g_k(x)=-\exp\!\left(-\frac{(k+1)L}{2}+\frac{x}{2}\right),\qquad 0<x<L.$$
--   For $0\le t\le L$ define its causal overlap contributions by
--   $$c_0(t)=\int_t^L g_0(x-t)g_0(x)\,dx,$$
--   $$c_{k+1}(t)=\int_0^t g_k(x-t+L)g_{k+1}(x)\,dx
--   +\int_t^L g_{k+1}(x-t)g_{k+1}(x)\,dx.$$
--   Then
--   $$c_0(t)=e^{-t/2}-e^{-L+t/2},$$
--   $$c_{k+1}(t)=e^{-(k+1)L}(1-e^{-L})e^{t/2},\qquad
--   \sum_{k=0}^{\infty}c_k(t)=e^{-t/2}.$$
--   The final assertion is convergence of the series to the stated value, including both endpoints of the allowed shift interval.
--
--   For $L=\log p$, these are the overlap kernels behind the first-cell term $M_f(-1/2)-p^{-1}M_f(1/2)$ and the subsequent-cell terms $p^{-k}(1-p^{-1})M_f(1/2)$ in the reference pole calculation. This theorem evaluates the explicit reference profile; identifying it with a pole direction of an actual global projection is a separate analytic obligation.
-- source:
--   Yi, 'The real half moment on the first global cell, and where its compensation goes', https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-d9bf59c5-5600-4dbe-9840-c2ca4f0e4293, the displayed formula g_p(kL+s)=-r^(k+1) exp(s/2) and the paragraph 'For f supported strictly in (0,L)'. The pointwise cell-overlap identity is the elementary integral calculation behind the two displayed reference pole-trace formulas; the global Hardy/theta identification is separate.

import Definitions.Def_MasulloRepair_PoleCells
set_option autoImplicit false
open MasulloRepair

theorem MasulloRepair.pole_cell_overlap (L : ℝ) (hL : 0 < L) (t : ℝ) (ht : t ∈ Set.Icc 0 L) :
    poleCellOverlap L 0 t = Real.exp (-t / 2) - Real.exp (-L + t / 2) ∧
    (∀ k : ℕ, poleCellOverlap L (k + 1) t =
      Real.exp (-L) ^ (k + 1) * (1 - Real.exp (-L)) * Real.exp (t / 2)) ∧
    HasSum (fun k : ℕ => poleCellOverlap L k t) (Real.exp (-t / 2)) := by sorry
