-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_entropyPair_of_matrix
-- name    : OAI.MetricEntropyDuality.entropyPair_of_matrix
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:14:03.394983+00:00
-- url     : https://prove2.me/theorems/d20ffba4-ef1e-4ef9-b0a8-df40ed63a788
-- title:
--   A separated finite-field matrix with short approximations yields an entropy pair
-- statement:
--   Let $a\ge1$, $r\ge1$, $B>0$, $h=h(a)$, $\theta=\theta(a)$, $s=\lceil1/\theta\rceil$, $u$ the direction count, $C$ the encoding cost and $D(r,k)=\binom{r+k-1}{k}$. Let $p$ be a prime with $p>\exp(BC/D(r,h))$. Let $g:Y\times X\to\mathbb R$ have $|X|=p^{D(r,h)}\le|Y|$ and separated rows (for $x\ne x'$ some $|g(y,x)-g(y,x')|\ge1$). Let $A$ be a $6\theta$-approximation of the $\ell_1$-ball column combinations with $|A|\le Q^2$, where
--   $$
--   \log Q\le hs\log\bigl(p^{D(r,h-1)}\bigr)+C .
--   $$
--   Then an entropy pair for $(a,r,B)$ exists: a symmetric convex body $K\subset\mathbb R^n$ with $n\ge r$, $N(K,Q_n)>1$ and entropy ratio $\log N(Q_n^\circ,a^{-1}K^\circ)/\log N(K,Q_n)$ in $[0,\beta(a,r,B))$.
--
--   This is the bridge from the combinatorial construction to the geometric statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/MatrixEntropy.lean#L26-L102

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
universe uX uY
open scoped Pointwise

theorem OAI.MetricEntropyDuality.entropyPair_of_matrix {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (a : ℝ) (ha : 1 ≤ a) (r : ℕ) (hr : 0 < r)
    (B : ℝ) (hB : 0 < B) (p : ℕ) (hp : p.Prime)
    (hprime : Real.exp (B * encodingCost (compressionRadius a) (accuracy a)
      (directionCount r (compressionRadius a) (accuracy a)) /
        (formDimension r (compressionRadius a) : ℝ)) < (p : ℝ))
    (g : Y → X → ℝ)
    (hrows : Fintype.card X = p ^ formDimension r (compressionRadius a))
    (hcolumns : Fintype.card X ≤ Fintype.card Y)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace X))
    (hA : UniformApproximation g (6 * accuracy a) A)
    (Q : ℕ) (hAQ : A.card ≤ Q ^ 2)
    (hQ : Real.log (Q : ℝ) ≤
      (compressionRadius a : ℝ) * (pivotSlots (accuracy a) : ℝ) *
        Real.log ((p : ℝ) ^ formDimension r (compressionRadius a - 1)) +
          encodingCost (compressionRadius a) (accuracy a)
            (directionCount r (compressionRadius a) (accuracy a))) :
    Nonempty (EntropyPair a r B) := by sorry
