-- Prove2me | Theorems.Thm_OAI_Dixmier_dimension_ratio_tendsto
-- name    : OAI.Dixmier.dimension_ratio_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:24:28.089323+00:00
-- url     : https://prove2.me/theorems/f0f84a03-c52f-4452-837b-4f60c358c76d
-- title:
--   The fibre dimension is negligible compared with $d^\ell$ when $\rho<1$
-- statement:
--   Fix an integer $d\ge2$ and a real number $\rho$ with $0\le\rho<1$. For $\ell\in\mathbb{N}$ define the endpoint capacity $r_\ell$ and the fibre dimension $k_\ell$ by
--
--   $$r_\ell=\big\lceil d^\ell\rho^\ell\big\rceil,\qquad k_\ell=\big\lceil 2\,r_\ell\,\log(2d^\ell)\big\rceil,$$
--
--   where $\log$ is the natural logarithm. Then
--
--   $$\lim_{\ell\to\infty}\frac{k_\ell}{d^\ell}=0 .$$
--
--   In the construction of uniformly bounded non-unitarizable representations, $d^\ell$ is the number of words of length $\ell$ over a $d$-letter alphabet, $r_\ell$ bounds how many of them a sparse mask may select, and $k_\ell$ is the dimension of the fibre $\mathbb{C}^{k_\ell}$ carrying a frame indexed by these words. The limit says that the fibre dimension is $o(d^\ell)$, which is what makes the kernel energy (at least $d^\ell$) unbounded relative to the fibre dimension.
--
--   **Formalization Note** $r_\ell$ and $k_\ell$ are `endpointCapacity d ρ ℓ` and `fiberDimension d ρ ℓ`, both defined with the natural-number ceiling `Nat.ceil`; the ratio is taken in $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Parameters.lean#L52-L72

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters

open OAI OAI.Dixmier
open Filter Topology

theorem OAI.Dixmier.dimension_ratio_tendsto {d : ℕ} (hd : 2 ≤ d) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun ℓ : ℕ => (fiberDimension d ρ ℓ : ℝ) / (d : ℝ)^ℓ) atTop (𝓝 0) := by sorry
