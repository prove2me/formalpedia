-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_exists_robust_directions_of_budget
-- name    : OAI.MetricEntropyDuality.exists_robust_directions_of_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:18:57.565989+00:00
-- url     : https://prove2.me/theorems/1063e37f-965a-423a-9fcd-999536a7f365
-- title:
--   Existence of robust directions for all nonzero forms
-- statement:
--   Let $p$ be prime, $r,h,u\ge1$, $\theta<1$, $D=\binom{r+h-1}{h}$, and suppose
--   $$
--   2hD\le\theta u,\qquad p>h,\qquad p>h^2u^{2h} .
--   $$
--   Then there are directions $t_1,\dots,t_u\in\mathbb F_p^r$ such that for every nonzero symmetric $h$-linear form $F$ there is a nonempty $T\subseteq\{1..u\}$ with $|\{1..u\}\setminus T|\le\theta u$ and
--   $$
--   F(t_{a_1},\dots,t_{a_h})\ne0\quad\text{for all }a_1,\dots,a_h\in T.
--   $$
--
--   Each nonzero form is nonvanishing on all tuples from a large set of directions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/RobustDirections.lean#L23-L95

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

open OAI OAI.MetricEntropyDuality

theorem OAI.MetricEntropyDuality.exists_robust_directions_of_budget
    {p r h u : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hh : 0 < h) (hu : 0 < u)
    {θ : ℝ} (hθ : θ < 1)
    (hdel : (h : ℝ) * (2 * (formDimension r h : ℝ)) ≤ θ * (u : ℝ))
    (hp_h : h < p) (hp_size : h ^ 2 * u ^ (2 * h) < p) :
    ∃ t : Fin u → Fin r → ZMod p,
      ∀ F : SymmetricForm (ZMod p) r h, F ≠ 0 →
        ∃ T : Finset (Fin u),
          ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ) ∧ T.Nonempty ∧
          ∀ a : Fin h → Fin u, (∀ j, a j ∈ T) →
            SymmetricForm.eval F (fun j => t (a j)) ≠ 0 := by sorry
