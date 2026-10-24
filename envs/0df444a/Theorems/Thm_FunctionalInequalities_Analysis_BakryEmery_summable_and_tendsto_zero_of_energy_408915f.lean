-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_summable_and_tendsto_zero_of_energy_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.summable_and_tendsto_zero_of_energy_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:28.334987+00:00
-- url     : https://prove2.me/theorems/be572944-0aaf-449d-88a7-963dc3088d60
-- title:
--   Summability and Vanishing of an Energy Sequence
-- statement:
--   This formalizes the summation conclusion of Corollary 3.5 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $L,\chi,v:\mathbb N\to\mathbb R$ and let $a\in\mathbb R$. Assume:
--
--   1. $a>0$.
--   2. $L_i\ge0$, $\chi_i\ge0$, and $v_i\ge0$ for every $i\in\mathbb N$.
--   3. For every $i$,
--      $$L_{i+1}+\chi_i+a v_i\le L_i.$$
--
--   Then both series $\sum_i v_i$ and $\sum_i\chi_i$ are summable, and
--
--   $$v_i\longrightarrow0\qquad(i\to\infty).$$
--
--   This is the abstract telescoping argument underlying the vanishing of the gradient-energy sequence in the tensor-energy iteration.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Corollary 3.5, p. 13. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/TensorEnergy.lean#L350-L381 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.TensorEnergy`, declaration `FunctionalInequalities.Analysis.BakryEmery.summable_and_tendsto_zero_of_energy`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
variable (m : Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.summable_and_tendsto_zero_of_energy_408915f {L χ v : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hL : ∀ i, 0 ≤ L i) (hχ : ∀ i, 0 ≤ χ i) (hv : ∀ i, 0 ≤ v i)
    (h45 : ∀ i, L (i + 1) + χ i + a * v i ≤ L i) :
    Summable v ∧ Summable χ ∧ Tendsto v atTop (𝓝 0) := by sorry
