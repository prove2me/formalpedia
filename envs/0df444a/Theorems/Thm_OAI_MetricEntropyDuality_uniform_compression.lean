-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_uniform_compression
-- name    : OAI.MetricEntropyDuality.uniform_compression
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:36:03.031439+00:00
-- url     : https://prove2.me/theorems/abad1c35-bd49-4e4a-85c7-bc360b994db9
-- title:
--   Uniform compression of the graph-profile matrix
-- statement:
--   Let $L_i:X\to\Lambda_i$ ($i\le u$) be label maps on a finite nonempty set $X$ and, for $T\subseteq\{1..u\}$, let $d_T$ be the extended distance of the partition graph in which distinct $x,y$ are adjacent when $L_i(x)=L_i(y)$ for some $i\in T$. Let $\varphi_h(d)=\max(0,1-\log(d+1)/\log(h+1))$ with $\varphi_h(\infty)=0$. Suppose every $L_i$ takes at most $q$ values. Let $\mathcal T$ be a family of sets $T$ with $|\{1..u\}\setminus T|\le\theta u$, and $g((v,T),x)=\varphi_h(d_T(x,v))$ the graph-profile matrix. Assume $u,q,h,s\ge1$, $\theta>0$, $s\theta\ge1$ and $\log3/\log(h+1)\le\theta$. Then there is a nonempty finite list $A$ of functions on $X$ with
--   $$
--   |A|\le u\,q^{hs}\Bigl(1+\frac{s2^u}{\theta}\Bigr)^{hs2^u}
--   $$
--   such that every combination $\sum_y\mu_yg(y,\cdot)$ with $\mu\ge0$, $\sum\mu\le1$ is within $3\theta$ of some member of $A$ in the sup norm.
--
--   The list size is independent of the number of rows $|X|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/Compression.lean#L123-L147

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
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode
import Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionDecoder
import Definitions.Def_OAI_Analysis_MetricEntropy_GroupedWeights
import Definitions.Def_OAI_Analysis_MetricEntropy_SignedCompression

open OAI OAI.MetricEntropyDuality
universe uX uY uLabel
open scoped BigOperators Classical
open CompressionLevels ProfileMixtures
variable {X : Type uX} {Y : Type uY} [Fintype X] [Nonempty X] [Fintype Y]
variable {u q h s : ℕ} {Label : Fin u → Type uLabel}

theorem OAI.MetricEntropyDuality.uniform_compression
    (L : (i : Fin u) → X → Label i)
    (hlabels : ∀ i, Nat.card (Set.range (L i)) ≤ q)
    (𝒯 : Finset (Finset (Fin u)))
    (hu : 0 < u) (hq : 0 < q) (hh : 0 < h) (hs : 0 < s)
    (θ : ℝ) (hθ : 0 < θ) (hsθ : 1 ≤ (s : ℝ) * θ)
    (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (hcomp : ∀ T ∈ 𝒯, ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ)) :
    ∃ A : Finset (X → ℝ), A.Nonempty ∧
      (A.card : ℝ) ≤ (u : ℝ) * (q : ℝ) ^ (h * s) *
        (1 + (s : ℝ) * 2 ^ u / θ) ^ (h * s * 2 ^ u) ∧
      SignedCompression.PositiveApproximation (GraphProfile.column L 𝒯 h) θ A := by sorry
