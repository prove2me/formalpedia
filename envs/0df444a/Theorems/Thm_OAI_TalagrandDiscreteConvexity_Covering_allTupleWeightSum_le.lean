-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_allTupleWeightSum_le
-- name    : OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:59:45.392165+00:00
-- url     : https://prove2.me/theorems/c62ba15d-767c-47b4-8f6b-02d9e4522078
-- title:
--   Geometric bound for the total weight of edge tuples
-- statement:
--   Let $H$ be a finite family of $r$-element subsets of $V$ and $\rho,T\ge0$. Write $A_t=\sum_{f:\{1,\dots,t\}\to H}\rho^{|\bigcup_if(i)|}$ for the total weight of unrestricted $t$-tuples of edges. Assume the extension bound: for every finite $B\subseteq V$,
--   $$
--   \sum_{e\in H}\rho^{|e\setminus B|}\le T(1+|B|)^r .
--   $$
--
--   Then for every $t\le m$,
--   $$
--   A_t\le\bigl(T(1+rm)^r\bigr)^t .
--   $$
--
--   Tuples of up to $m$ edges grow at most geometrically. Combined with the probability that a tuple survives the pair sampling, this bounds the residual cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringResidualTuples.lean#L161-L185

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples

open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

theorem OAI.TalagrandDiscreteConvexity.Covering.allTupleWeightSum_le (H : Family V) {rho T : ℝ} {r m : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T)
    (uniform : ∀ e ∈ H, (e : Finset V).card = r)
    (extension : ∀ B : Finset V,
      (∑ e ∈ H, rho ^ (e \ B).card) ≤ T * (1 + (B.card : ℝ)) ^ r)
    (t : ℕ) (ht : t ≤ m) :
    allTupleWeightSum H rho t ≤ (T * (1 + ((r * m : ℕ) : ℝ)) ^ r) ^ t := by sorry
