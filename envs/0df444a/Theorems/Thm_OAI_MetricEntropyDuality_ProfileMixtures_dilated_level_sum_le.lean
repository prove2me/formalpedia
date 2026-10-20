-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_ProfileMixtures_dilated_level_sum_le
-- name    : OAI.MetricEntropyDuality.ProfileMixtures.dilated_level_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:31:34.391527+00:00
-- url     : https://prove2.me/theorems/a2b81e01-1857-4e31-b9c6-40c1a06c229f
-- title:
--   Dilated level sums are controlled by the profile mixture
-- statement:
--   Let $L_i:X\to\Lambda_i$ be label maps and, for a set $T$ of indices, let $d_T$ be the extended distance of the partition graph in which distinct $x,y$ are adjacent when $L_i(x)=L_i(y)$ for some $i\in T$. Columns $y$ have centres $v_y\in X$, label sets $T_y$ and weights $\mu_y\ge0$. The level value is $\ell_j(x)=\sum_y\mu_y\mathbf 1[d_{T_y}(x,v_y)\le j]$, and the profile mixture is $M(x)=\sum_y\mu_y\varphi_h(d_{T_y}(x,v_y))$ with $\varphi_h(d)=\sum_{j<h}\gamma_h(j)\mathbf 1[d\le j]$, $\gamma_h(j)=\frac{\log(j+2)-\log(j+1)}{\log(h+1)}$. Assume $\sum_y\mu_y\le1$, $h\ge1$, $\theta\ge0$ and $\log3/\log(h+1)\le\theta$. Then for every $x$,
--   $$
--   \sum_{j<h}\gamma_h(j)\,\ell_{3j+2}(x)\le M(x)+\theta .
--   $$
--
--   Dilating every level to radius $3j+2$ overestimates the profile mixture by at most $\theta$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/ProfileMixtures.lean#L82-L113

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.ProfileMixtures
universe uX uY uι uLabel uJ
open scoped BigOperators
variable {X : Type uX} {Y : Type uY} {ι : Type uι} {Label : ι → Type uLabel} [Fintype Y]

theorem OAI.MetricEntropyDuality.ProfileMixtures.dilated_level_sum_le (L : (i : ι) → X → Label i) (v : Y → X)
    (T : Y → Finset ι) (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    (hmass : ∑ y, μ y ≤ 1) {h : ℕ} (hh : 0 < h) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ) (x : X) :
    (∑ j : Fin h, LogProfile.gamma h j.val *
      CompressionLevels.levelValue L v T μ (3 * j.val + 2) x) ≤
        profileMixture L v T h μ x + θ := by sorry
