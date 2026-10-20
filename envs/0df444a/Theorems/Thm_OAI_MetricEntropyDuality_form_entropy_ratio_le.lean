-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_form_entropy_ratio_le
-- name    : OAI.MetricEntropyDuality.form_entropy_ratio_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:07:20.307591+00:00
-- url     : https://prove2.me/theorems/5cb765d6-ca1a-4acb-9ebe-a66e880bb0e2
-- title:
--   Entropy ratio bound from the compression count
-- statement:
--   Let $r,h\ge1$, $p>1$, $s\in\mathbb N$, $C\in\mathbb R$, and $D(r,h)=\binom{r+h-1}{h}$. Suppose $\log Q\le hs\log\bigl(p^{D(r,h-1)}\bigr)+C$. Then
--   $$
--   \frac{\log(Q^2)}{\log\bigl(p^{D(r,h)}\bigr)}\le\frac{2h^2s}{r+h-1}+\frac{2C}{D(r,h)\log p} .
--   $$
--
--   A squared compression list is negligible against $p^{D(r,h)}$ rows once $r\gg h^2s$ and $p$ is large.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/EntropyBounds.lean#L75-L94

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

open OAI OAI.MetricEntropyDuality
universe uα

theorem OAI.MetricEntropyDuality.form_entropy_ratio_le {r h s p Q : ℕ} {C : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hp : 1 < p)
    (hQ : Real.log (Q : ℝ) ≤ (h : ℝ) * (s : ℝ) *
      Real.log ((p : ℝ) ^ formDimension r (h - 1)) + C) :
    Real.log ((Q : ℝ) ^ 2) / Real.log ((p : ℝ) ^ formDimension r h) ≤
      2 * (h : ℝ) ^ 2 * (s : ℝ) / ((r : ℝ) + h - 1) +
        2 * C / ((formDimension r h : ℝ) * Real.log (p : ℝ)) := by sorry
