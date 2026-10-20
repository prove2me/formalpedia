-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_exists_prime_for_rank
-- name    : OAI.MetricEntropyDuality.exists_prime_for_rank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:12:37.779347+00:00
-- url     : https://prove2.me/theorems/2d1ca165-40a7-4ae4-8f8a-91dbf7ea7013
-- title:
--   Choosing the prime after all other parameters
-- statement:
--   Let $a\ge1$, $r\ge1$, $B>0$ and $\mathrm{bound}\in\mathbb R$. Let $h=h(a)$ be the compression radius, $D=\binom{r+h-1}{h}$, $\theta=\theta(a)$, $u=u(r,h,\theta)$ the direction count, and $C=C(h,\theta,u)$ the encoding cost. Then there is a prime $p>\mathrm{bound}$ with $p>h$, $p>h^2u^{2h}$ and
--   $$
--   p>\exp(BC/D),
--   $$
--   and consequently $\log p>0$, $BC<D\log p$, $\dfrac{2C}{D\log p}<\dfrac2B$ and $C>0$.
--
--   All other parameters are fixed first, and the field size is chosen last.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/PrimeChoice.lean#L77-L100

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

open OAI OAI.MetricEntropyDuality

theorem OAI.MetricEntropyDuality.exists_prime_for_rank {a : ℝ} (ha : 1 ≤ a) {r : ℕ} (hr : 0 < r)
    (B bound : ℝ) (hB : 0 < B) :
    let h := compressionRadius a
    let D := formDimension r h
    let u := directionCount r h (accuracy a)
    let C := encodingCost h (accuracy a) u
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) ∧ h < p ∧
      h ^ 2 * u ^ (2 * h) < p ∧ Real.exp (B * C / (D : ℝ)) < (p : ℝ) ∧
      0 < Real.log (p : ℝ) ∧ B * C < (D : ℝ) * Real.log (p : ℝ) ∧
      2 * C / ((D : ℝ) * Real.log (p : ℝ)) < 2 / B ∧ 0 < C := by sorry
