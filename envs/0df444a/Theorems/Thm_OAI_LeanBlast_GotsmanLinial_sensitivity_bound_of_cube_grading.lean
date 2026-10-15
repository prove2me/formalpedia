-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sensitivity_bound_of_cube_grading
-- name    : OAI.LeanBlast.GotsmanLinial.sensitivity_bound_of_cube_grading
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:00:03.151008+00:00
-- url     : https://prove2.me/theorems/fabb92ac-c527-45b8-b55a-0d79e57c364a
-- title:
--   Average sensitivity bound $8d\sqrt{n}$ from a binomial tridiagonal grading with vanishing low blocks
-- statement:
--   Let $n, d$ be natural numbers. Identify the Boolean cube with $\{-1,1\}^n$, write $x_i$ for the coordinates of a vertex $x$ and $x^{\oplus i}$ for the vertex obtained from $x$ by flipping coordinate $i$. For $f : \{-1,1\}^n \to \mathbb{R}$ the average sensitivity is
--   $$
--   \mathrm{AS}(f) = \sum_{i=1}^{n} \frac{\#\{x \in \{-1,1\}^n : f(x) \neq f(x^{\oplus i})\}}{2^n}.
--   $$
--   Consider complex matrices whose rows and columns are indexed by the $2^n$ vertices. Let $Z_i = \operatorname{diag}(x_i)$ be the $i$-th coordinate sign matrix, let $\chi(x) = \prod_{i=1}^n x_i$ be the full parity, and for a real function $g$ on the cube write $\operatorname{diag}(g)$ for the diagonal matrix with entries $g(x)$. Assume:
--
--   1. $f(x) \in \{1, -1\}$ for every vertex $x$;
--   2. $P_0, P_1, \dots, P_n$ is an orthogonal projection family: every $P_k$ is Hermitian and idempotent, $P_r P_s = 0$ for $r \neq s$, and $\sum_{k=0}^{n} P_k = I$;
--   3. $\operatorname{Re}\operatorname{tr} P_k = \binom{n}{k}$ for every $k \in \{0,\dots,n\}$;
--   4. every $Z_i$ is block tridiagonal: $P_s Z_i P_r = 0$ whenever $r + 1 < s$ or $s + 1 < r$;
--   5. low blocks of the parity-twisted function vanish: $P_s \operatorname{diag}(\chi f)\, P_r = 0$ for all $r, s \in \{0,\dots,n\}$ with $r + s < n - d$.
--
--   Then
--
--   $$
--   \mathrm{AS}(f) \le 8\, d\, \sqrt{n}.
--   $$
--
--   This isolates the matrix-analytic core of the Gotsman–Linial bound: any orthogonal grading of $\mathbb{C}^{\{-1,1\}^n}$ with binomial multiplicities, in which coordinate signs move the grading by at most one step and the parity-twisted Boolean function has no blocks below the antidiagonal $r + s = n - d$, forces average sensitivity at most $8d\sqrt{n}$. The polynomial-threshold case is then obtained by constructing such a grading from a weighted Walsh flag.
--
--   **Formalization Note** The cube is `Cube n = Fin n → Bool`, with `true` read as $1$ and `false` as $-1$; the hypotheses are `OrthogonalProjectionFamily P`, a condition on the real part of `Matrix.trace (P k)`, `BlockTridiagonal P (coordinateSignMatrix i)`, and a vanishing condition for `signMatrix (fun x => fullParity x * f x)`. Here $n - d$ is truncated natural subtraction (so condition 5 is empty when $d \ge n$), and no further restriction on $n$ or $d$ is imposed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Main.lean#L47-L90

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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WalshDimensions
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WeightedGrading
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_GradingShift

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators

theorem OAI.LeanBlast.GotsmanLinial.sensitivity_bound_of_cube_grading {n d : ℕ}
    (f : Cube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (P : Fin (n + 1) → Matrix (Cube n) (Cube n) ℂ)
    (hP : OrthogonalProjectionFamily P)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (htri : ∀ i : Fin n, BlockTridiagonal P (coordinateSignMatrix i))
    (hvanish : ∀ r s : Fin (n + 1), r.val + s.val < n - d →
      P s * signMatrix (fun x => fullParity x * f x) * P r = 0) :
    averageSensitivity f ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by sorry
