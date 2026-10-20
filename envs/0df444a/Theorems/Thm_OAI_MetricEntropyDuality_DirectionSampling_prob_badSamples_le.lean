-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_DirectionSampling_prob_badSamples_le
-- name    : OAI.MetricEntropyDuality.DirectionSampling.prob_badSamples_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:15:55.479376+00:00
-- url     : https://prove2.me/theorems/9588a019-0f2d-4ae0-996a-9820ae4b4278
-- title:
--   Union bound for disjoint bad-tuple witnesses
-- statement:
--   For finite sets $U$ and $E\ne\varnothing$, the sample space is $E^U$ with uniform probability $\Pr(A)=|A|/|E|^{|U|}$; an event $A$ depends only on $S\subseteq U$ if samples agreeing on $S$ are both in $A$ or both outside it. Sample directions $t\in E^{\{1..u\}}$ uniformly. Let $Z$ be a finite set of forms, $\mathrm{bad}(z,\cdot)$ a property of $h$-tuples of values, and $b\ge0$ with $\Pr[\mathrm{bad}(z,t\circ a)]\le b$ for every $z\in Z$ and every tuple $a\in\{1..u\}^h$. Then the probability that some $z\in Z$ has $w$ bad tuples with pairwise disjoint supports satisfies
--   $$
--   \Pr(\text{bad sample})\le|Z|\,u^{hw}\,b^w .
--   $$
--
--   Requiring disjoint supports turns a union bound over lists into a product of independent small probabilities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/DirectionSampling.lean#L142-L171

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

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.DirectionSampling
universe uU uE uJ uZ
open scoped BigOperators
open FiniteProductCounting
variable {Z : Type uZ} {E : Type uE} [Fintype E] [DecidableEq E] [Nonempty E]
  {u h w : ℕ}

theorem OAI.MetricEntropyDuality.DirectionSampling.prob_badSamples_le (forms : Finset Z) (bad : Z → (Fin h → E) → Prop)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ z ∈ forms, ∀ a : Fin h → Fin u, prob (tupleEvent (bad z) a) ≤ b) :
    prob (badSamples (u := u) (w := w) forms bad) ≤
      (forms.card : ℝ) * (u : ℝ) ^ (h * w) * b ^ w := by sorry
