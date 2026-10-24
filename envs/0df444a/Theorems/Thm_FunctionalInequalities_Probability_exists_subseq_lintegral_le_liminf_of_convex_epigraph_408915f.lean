-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_exists_subseq_lintegral_le_liminf_of_convex_epigraph_408915f
-- name    : FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:26.002265+00:00
-- url     : https://prove2.me/theorems/eb5fa145-f7ee-40d0-9ede-06c62ce651bd
-- title:
--   Subsequence Compactness For Extended-Real Convex Potentials
-- statement:
--   This formalizes the first half, (56a), of Lemma 17 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as “Compactness of normalised potentials.”
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $\mu$ be a finite measure such that $0$ lies in the interior of the convex hull of its support. Let $\phi_j:E\to\overline{\mathbb R}$ satisfy:
--
--   1. $\phi_j(x)\ge0$ for every $j,x$.
--   2. $\phi_j(0)=0$.
--   3. Each real epigraph of $\phi_j$ is convex.
--   4. Each $x\mapsto(\phi_j(x)).\operatorname{toENNReal}$ is a.e. measurable.
--   5. The supremum of their lower integrals is finite:
--      $$\sup_j\int^- (\phi_j(x)).\operatorname{toENNReal}\,d\mu(x)\ne+\infty.$$
--
--   Then there are a strictly increasing subsequence map $s:\mathbb N\to\mathbb N$ and $\psi:E\to\overline{\mathbb R}$ such that $\psi\ge0$, $\psi(0)=0$, its real epigraph is convex, and $\psi.\operatorname{toENNReal}$ is measurable. On the interior of the support convex hull, $\psi$ is finite and
--   $$\phi_{s(j)}(x)\longrightarrow\psi(x).$$
--   Moreover, $\psi$ is radially closed, equals $+\infty$ outside the closure of that interior, and
--   $$\int^-\psi(x).\operatorname{toENNReal}\,d\mu(x)\le\liminf_{j\to\infty}\int^- (\phi_{s(j)}(x)).\operatorname{toENNReal}\,d\mu(x).$$
--
--   This is the compactness and lower-integral part of the convex-potential argument.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 17. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Compactness.lean#L105-L227 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Compactness`, declaration `FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

open MeasureTheory
open scoped ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability

theorem FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
    (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
    (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
    (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
    ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
      Measurable (fun x => (ψ x).toENNReal) ∧
      (∀ x ∈ interior (convexHull ℝ μ.support),
        ψ x ≠ ⊤ ∧ Filter.Tendsto (fun j => φ (s j) x) Filter.atTop (nhds (ψ x))) ∧
      (∀ x, Filter.Tendsto (fun t : ℝ => ψ (t • x)) (nhdsWithin 1 (Set.Iio 1)) (nhds (ψ x))) ∧
      (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
      ∫⁻ x, (ψ x).toENNReal ∂μ ≤
        Filter.liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) Filter.atTop := by sorry
