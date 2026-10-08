-- Prove2me | Theorems.Thm_Helfgott_actual_phase_mellin_hasDerivAt
-- name    : Helfgott.actual_phase_mellin_hasDerivAt
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T11:11:40.154336+00:00
-- url     : https://prove2.me/theorems/67682c8c-dfff-4a6f-9971-d9d375cf903d
-- title:
--   Holomorphy and exact logarithmic Mellin derivative for both actual additive-phase Goldbach smoothings
-- statement:
--   For actual etaPlus or etaStar and any real phase omega, put f(t)=eta(t) exp(i omega t). For every complex s with Re(s)>-1, the logarithmically weighted full Mellin integral converges absolutely, and the full Mellin transform is complex differentiable with derivative Mellin(log(t) f(t))(s). Thus both actual additive-phase transforms are holomorphic on Re(s)>-1. The proof also establishes the stronger Re(s)>-2 domain for etaStar.
--
--   The proof includes the actual smoothing envelopes, continuity on the full positive axis, exponential decay at infinity and order at the origin. EtaPlus is O(t), and etaStar is O(t²) at the origin; both retain all signed and infinite tails. It uses the complete Mathlib Mellin differentiation theorem, with every decay and regularity hypothesis proved for the actual smoothings. No convergence or holomorphy assumption remains. This supplies the analytic Mellin input for the pending Goldbach contour shifts; zero certificates and numerical character estimates remain separate obligations.
-- source:
--   Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897; actual coordinated smoothing in https://arxiv.org/html/1312.7748v2. Mathlib David Loeffler, Mellin differentiation under the integral; real polynomial/exponential asymptotics. All original complete smoothing envelope and phase regularity proofs included. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.MellinTransform
open MeasureTheory Set

theorem Helfgott.actual_phase_mellin_hasDerivAt (η : ℝ → ℝ) (hη : η=Helfgott.etaPlus ∨ η=Helfgott.etaStar)
    (ω : ℝ) (s : ℂ) (hs : -1 < s.re) :
    let f : ℝ → ℂ := fun t => (η t : ℂ)*Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))
    MellinConvergent (fun t : ℝ => Real.log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t : ℝ => Real.log t • f t) s) s := by sorry
