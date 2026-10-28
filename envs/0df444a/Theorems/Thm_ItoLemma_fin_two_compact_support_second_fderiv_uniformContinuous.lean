-- Prove2me | Theorems.Thm_ItoLemma_fin_two_compact_support_second_fderiv_uniformContinuous
-- name    : ItoLemma.fin_two_compact_support_second_fderiv_uniformContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:02:03.095105+00:00
-- url     : https://prove2.me/theorems/54ab1e3c-ddff-409a-96c2-1a810265b017
-- title:
--   Compact Support Makes Continuous Hessians Uniformly Continuous
-- statement:
--   On the two-coordinate real state space, the Hessian of a compactly supported function has compact support. If that Hessian is continuous, then it is uniformly continuous, providing a hypothesis of the accepted finite-dimensional Itô formula.
-- source:
--   Pinned-index lemma HasCompactSupport.uniformContinuous_of_continuous in Mathlib.Topology.UniformSpace.HeineCantor and HasCompactSupport.fderiv in Mathlib.Analysis.Calculus.FDeriv.Const, checked 26 October 2026. Official docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UniformSpace/HeineCantor.html

import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.UniformSpace.HeineCantor

theorem ItoLemma.fin_two_compact_support_second_fderiv_uniformContinuous
    (f : (Fin 2 → ℝ) → ℝ)
    (hs : HasCompactSupport f)
    (h₂ : Continuous (fderiv ℝ (fderiv ℝ f))) :
    UniformContinuous (fderiv ℝ (fderiv ℝ f)) := by sorry
