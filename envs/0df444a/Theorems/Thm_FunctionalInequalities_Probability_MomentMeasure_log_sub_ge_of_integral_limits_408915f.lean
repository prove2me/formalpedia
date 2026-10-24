-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_log_sub_ge_of_integral_limits_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:23.786131+00:00
-- url     : https://prove2.me/theorems/96a5193e-4a00-498a-a811-0ebdcbc68863
-- title:
--   Limit Assembly for Logarithmic Mass Comparison
-- statement:
--   This is an auxiliary limit-assembly statement related to Proposition 12 of Cordero–Klartag (arXiv:1304.0630v1).
--
--   Let $a:\mathbb{N}\to[0,\infty]$, $m:\mathbb{N}\to\mathbb{R}$, $Z\in[0,\infty]$, and $r,S,M\in\mathbb{R}$. Assume:
--
--   1. $0\le m_j$ for every $j$.
--   2. $\log a_j-m_j$ converges in the extended real line to $S$.
--   3. $m_j$ converges to $M$.
--   4. $\operatorname{ofReal}(r)\le\liminf_j\operatorname{ofReal}(m_j)$ in $[0,\infty]$.
--   5. $\limsup_j a_j\le Z$.
--
--   Then $Z>0$ and
--
--   $$
--   S\le \log Z-r.
--   $$
--
--   The declaration is a technical assembly lemma for passing from sequence limits and liminf/limsup bounds to a functional comparison; it is not an attainment statement.
--
--   **Formalization Note.** The quantities involving $a_j$ and $Z$ use `ENNReal.log`, while the subtraction and the comparison with $S$ and $r$ take place in `EReal`; the conclusion is expressed with the corresponding coercions.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L206-L241 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter
open scoped ENNReal Topology

theorem FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits_408915f
    (a : ℕ → ℝ≥0∞) (m : ℕ → ℝ) (Z : ℝ≥0∞) (r S M : ℝ)
    (hnn : ∀ j, 0 ≤ m j)
    (hF : Tendsto (fun j => ENNReal.log (a j) - (m j : EReal)) atTop (𝓝 (S : EReal)))
    (hm : Tendsto m atTop (𝓝 M))
    (hfirst : ENNReal.ofReal r ≤ liminf (fun j => ENNReal.ofReal (m j)) atTop)
    (hsecond : limsup a atTop ≤ Z) :
    0 < Z ∧ (S : EReal) ≤ ENNReal.log Z - (r : EReal) := by sorry
