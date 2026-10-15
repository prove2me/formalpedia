-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_binomial_block_coupling_bound
-- name    : OAI.LeanBlast.GotsmanLinial.binomial_block_coupling_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:44:03.941743+00:00
-- url     : https://prove2.me/theorems/6838b0cf-3e38-4773-a199-54a10b3a65a6
-- title:
--   Quadratic bound for nonnegative masses with binomial row and column sums vanishing below the antidiagonal $r+s=n-d$
-- statement:
--   Let $n,d\in\mathbb{N}$ and let $B=(B_{r,s})_{0\le r,s\le n}$ be a real $(n+1)\times(n+1)$ array such that
--
--   1. $B_{r,s}\ge0$ for all $r,s$;
--   2. all row and column sums are binomial coefficients: $\sum_{s=0}^{n}B_{r,s}=\binom nr$ for every $r$, and $\sum_{r=0}^{n}B_{r,s}=\binom ns$ for every $s$;
--   3. $B$ vanishes strictly below the antidiagonal $r+s=n-d$: $B_{r,s}=0$ whenever $r+s<n-d$, where $n-d$ is read as $0$ when $d>n$.
--
--   Then
--
--   $$
--   \sum_{r=0}^{n}\sum_{s=0}^{n}(r+s-n)^2\,B_{r,s}\;\le\;4\,d\,\sqrt n\;2^{n}.
--   $$
--
--   After division by $2^n$ the array $B$ is a coupling of two symmetric binomial $\mathrm{Bin}(n,\tfrac12)$ laws, and the statement says that if the coupled indices satisfy $r+s\ge n-d$ almost surely, then $\mathbb{E}(r+s-n)^2\le4d\sqrt n$. In the Gotsman–Linial argument the masses $B_{r,s}$ are the squared Hilbert–Schmidt norms of the blocks of a unitary sign matrix relative to a grading with binomial multiplicities, and the left-hand side is the Hilbert–Schmidt energy of its anticommutator with the centred grading; this yields the energy bound of order $d\sqrt n\,2^n$.
--
--   **Formalization Note** Indices range over `Fin (n + 1)`. The vanishing hypothesis uses natural-number subtraction `n - d`, which truncates at $0$; when $d\ge n$ that hypothesis is vacuous and the inequality still holds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/BlockCoupling.lean#L62-L133

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators

theorem OAI.LeanBlast.GotsmanLinial.binomial_block_coupling_bound
    (n d : ℕ) (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hB : ∀ r s, 0 ≤ B r s)
    (hrow : ∀ r, (∑ s : Fin (n + 1), B r s) = (n.choose r.val : ℝ))
    (hcol : ∀ s, (∑ r : Fin (n + 1), B r s) = (n.choose s.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → B r s = 0) :
    (∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      ((s.val : ℝ) + (r.val : ℝ) - (n : ℝ)) ^ 2 * B r s) ≤
        4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by sorry
