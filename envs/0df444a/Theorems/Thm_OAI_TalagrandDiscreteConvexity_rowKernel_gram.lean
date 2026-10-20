-- Prove2me | Theorems.Thm_OAI_TalagrandDiscreteConvexity_rowKernel_gram
-- name    : OAI.TalagrandDiscreteConvexity.rowKernel_gram
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:10:36.578128+00:00
-- url     : https://prove2.me/theorems/6e54001e-2981-405b-98b2-0adb76337345
-- title:
--   Orthogonality of the biased row kernels
-- statement:
--   Let $V$ be finite and $0<q<1$. With $\gamma_q(0)=1-q$, $\gamma_q(1)=-(1-q)$, bit masses $q$ (for $1$) and $1-q$ (for $0$), and the row kernel $K_U(x)=\prod_{i\in U}\gamma_q(x_i)\prod_{i\notin U}\mathrm{mass}_q(x_i)$, for all $x,y\in\{0,1\}^V$,
--   $$
--   \sum_{U\subseteq V}\Bigl(\frac{q}{1-q}\Bigr)^{|U|}K_U(x)K_U(y)=\begin{cases}\mu_q(x),&x=y,\\0,&x\ne y,\end{cases}
--   $$
--   where $\mu_q(x)=\prod_i\mathrm{mass}_q(x_i)$.
--
--   This is the Gram identity behind the biased Parseval formula for the coefficients $b_q(f,U)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/FourierProductKernel.lean#L49-L83

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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights

open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem OAI.TalagrandDiscreteConvexity.rowKernel_gram (q : ℝ) (_hq0 : 0 < q) (hq1 : q < 1) (x y : V → Bool) :
    (∑ U : Finset V,
      (q / (1 - q)) ^ U.card * rowKernel q U x * rowKernel q U y) =
      if x = y then cubeWeight q x else 0 := by sorry
