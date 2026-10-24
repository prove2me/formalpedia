-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_subseq_integral_bounds_of_convex_epigraph_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:26.464444+00:00
-- url     : https://prove2.me/theorems/34c0b0f8-3dcc-4ad7-b743-8abf76297e83
-- title:
--   Full Integral And Conjugate-Mass Compactness Bounds
-- statement:
--   This formalizes Lemma 17, (56), of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as “Compactness of normalised potentials.”
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure. Let $dx$ be an additive Haar measure, let $\mu$ be a finite measure, and assume $0$ lies in the interior of the convex hull of $\operatorname{supp}(\mu)$. Let $\phi_j:E\to\overline{\mathbb R}$ satisfy:
--
--   1. $\phi_j\ge0$ and $\phi_j(0)=0$.
--   2. Every real epigraph of $\phi_j$ is convex.
--   3. Each $\phi_j.\operatorname{toENNReal}$ is a.e. measurable with respect to $\mu$.
--   4. $\sup_j\int^-\phi_j.\operatorname{toENNReal}\,d\mu\ne+\infty$.
--
--   Then there exist a strictly increasing $s:\mathbb N\to\mathbb N$ and $\psi:E\to\overline{\mathbb R}$ such that $\psi\ge0$, $\psi(0)=0$, its real epigraph is convex, and $\psi.\operatorname{toENNReal}$ is measurable. On the interior of the support convex hull, $\psi$ is finite and
--   $$\phi_{s(j)}(x)\longrightarrow\psi(x).$$
--   The function $\psi$ is radially closed and equals $+\infty$ outside the closure of that interior. In addition, `PotentialIntegrable ψ μ` holds,
--   $$\operatorname{mass}(dx,\psi^*)\ne+\infty,$$
--   $$\int^-\psi.\operatorname{toENNReal}\,d\mu\le\liminf_{j\to\infty}\int^-\phi_{s(j)}.\operatorname{toENNReal}\,d\mu,$$
--   and
--   $$\limsup_{j\to\infty}\operatorname{mass}(dx,\phi_{s(j)}^*)\le\operatorname{mass}(dx,\psi^*).$$
--
--   This declaration combines the pointwise compactness, integral lower semicontinuity, and conjugate-mass upper semicontinuity conclusions; it does not assert variational attainment.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 17. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Compactness.lean#L239-L284 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Compactness`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph`; the repository is private at upload time).

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
noncomputable section
open Filter
open scoped Topology
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

theorem FunctionalInequalities.Probability.MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph_408915f
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (φ : ℕ → E → EReal) (hnn : ∀ ℓ x, 0 ≤ φ ℓ x) (hφ0 : ∀ ℓ, φ ℓ 0 = 0)
    (hconv : ∀ ℓ, Convex ℝ {p : E × ℝ | φ ℓ p.1 ≤ (p.2 : EReal)})
    (hmeas : ∀ ℓ, AEMeasurable (fun x => (φ ℓ x).toENNReal) μ)
    (hbdd : (⨆ ℓ, ∫⁻ x, (φ ℓ x).toENNReal ∂μ) ≠ ⊤) :
    ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
      Measurable (fun x => (ψ x).toENNReal) ∧
      (∀ x ∈ interior (convexHull ℝ μ.support),
        ψ x ≠ ⊤ ∧ Tendsto (fun j => φ (s j) x) atTop (𝓝 (ψ x))) ∧
      (∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x))) ∧
      (∀ x ∉ closure (interior (convexHull ℝ μ.support)), ψ x = ⊤) ∧
      PotentialIntegrable ψ μ ∧ mass dx (legendre ψ) ≠ ⊤ ∧
      (∫⁻ x, (ψ x).toENNReal ∂μ ≤
        liminf (fun j => ∫⁻ x, (φ (s j) x).toENNReal ∂μ) atTop) ∧
      limsup (fun j => mass dx (legendre (φ (s j)))) atTop ≤ mass dx (legendre ψ) := by sorry
