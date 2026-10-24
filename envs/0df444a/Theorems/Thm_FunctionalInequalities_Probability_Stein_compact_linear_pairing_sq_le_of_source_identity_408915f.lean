-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Stein_compact_linear_pairing_sq_le_of_source_identity_408915f
-- name    : FunctionalInequalities.Probability.Stein.compact_linear_pairing_sq_le_of_source_identity_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:22:29.480102+00:00
-- url     : https://prove2.me/theorems/fa2a3320-08cc-4dde-96ab-4e9d96db3628
-- title:
--   Squared Dual Pairing Bound from a Source Identity
-- statement:
--   This statement gives a squared dual pairing estimate from a latent source identity.
--
--   Let $Ω$ be a measurable space with measure $P$, let $μ$ be a probability measure on $\mathbb R^n$, and let $Z,F:Ω\to\mathbb R^n$. Assume:
--
--   1. $Z$ is measurable and `map Z P = μ`;
--   2. $F\in L^2(P)$;
--   3. $v\in\mathbb R^n$ and $h:\mathbb R^n\to\mathbb R$ is smooth with compact support;
--   4. the source identity holds:
--
--   $$
--   \int \langle x,v\rangle h(x)\,dμ(x)
--   =
--   \int \langle F(w),∇h(Z(w))\rangle\,dP(w).
--   $$
--
--   Then
--
--   $$
--   \left(\int \langle x,v\rangle h(x)\,dμ(x)\right)^2
--   \le
--   \left(\int \|F(w)\|^2\,dP(w)\right)
--   \left(\int \|Dh(x)\|^2\,dμ(x)\right).
--   $$
--
--   Here the derivative norm is expressed in Lean as `‖fderiv ℝ h x‖`. The result is a general latent-space Cauchy–Schwarz bound and does not assume that $Z$ is invertible.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.9. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Stein/SourceDualBound.lean#L22-L63 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Stein.SourceDualBound`, declaration `FunctionalInequalities.Probability.Stein.compact_linear_pairing_sq_le_of_source_identity`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace Topology ContDiff
section CompactSourceDualBound
open MeasureTheory Filter
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 400000

theorem FunctionalInequalities.Probability.Stein.compact_linear_pairing_sq_le_of_source_identity_408915f
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (Z F : Ω → EuclideanSpace ℝ (Fin n)) (hZ : Measurable Z)
    (hmap : P.map Z = (mu : Measure (EuclideanSpace ℝ (Fin n))))
    (hF : MemLp F 2 P) (v : EuclideanSpace ℝ (Fin n))
    (h : EuclideanSpace ℝ (Fin n) → ℝ) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (hid : (∫ x, ⟪x, v⟫ * h x ∂(mu : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ w, ⟪F w, gradient h (Z w)⟫ ∂P) :
    (∫ x, ⟪x, v⟫ * h x ∂(mu : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2 ≤
      (∫ w, ‖F w‖ ^ 2 ∂P) *
        ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(mu : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
