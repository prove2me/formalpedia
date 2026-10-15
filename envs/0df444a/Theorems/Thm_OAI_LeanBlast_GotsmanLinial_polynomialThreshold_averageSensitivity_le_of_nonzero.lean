-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_polynomialThreshold_averageSensitivity_le_of_nonzero
-- name    : OAI.LeanBlast.GotsmanLinial.polynomialThreshold_averageSensitivity_le_of_nonzero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:00:40.274705+00:00
-- url     : https://prove2.me/theorems/5cdc7851-e168-4e3c-89e1-359ae681dc80
-- title:
--   Gotsman–Linial bound for multilinear polynomials with no zeros on the cube
-- statement:
--   Identify the Boolean cube with $\{-1,1\}^n$, write $x^{\oplus i}$ for the vertex obtained from $x$ by flipping coordinate $i$, and let $\operatorname{sgn}(t) = 1$ for $t \ge 0$ and $\operatorname{sgn}(t) = -1$ for $t < 0$. Let $n, d$ be natural numbers and let $p \in \mathbb{R}[X_1,\dots,X_n]$ be multilinear (every monomial in its support has exponent at most $1$ in each variable) with total degree at most $d$. Assume that $p(x) \neq 0$ for every $x \in \{-1,1\}^n$. Then the polynomial threshold function $f = \operatorname{sgn}\circ p$ satisfies
--
--   $$
--   \mathrm{AS}(\operatorname{sgn}\circ p) \;=\; \sum_{i=1}^{n} \frac{\#\{x \in \{-1,1\}^n : \operatorname{sgn} p(x) \neq \operatorname{sgn} p(x^{\oplus i})\}}{2^n} \;\le\; 8\, d\, \sqrt{n}.
--   $$
--
--   This is the Gotsman–Linial average-sensitivity bound for degree-$d$ polynomial threshold functions under the additional assumption that $p$ does not vanish on the cube; that assumption is removed afterwards by adding a small positive constant to $p$. No condition such as $1 \le d \le n$ is needed.
--
--   **Formalization Note** Cube vertices are `Fin n → Bool`, read as sign vectors with `true` as $1$ and `false` as $-1$; `polynomialValue p x` evaluates $p$ at this sign vector and `polynomialThreshold p` is `thresholdSign` composed with it. Multilinearity is the predicate `IsMultilinear p` on the support of the `MvPolynomial`, and the degree bound is `p.totalDegree ≤ d`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Main.lean#L92-L109

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

theorem OAI.LeanBlast.GotsmanLinial.polynomialThreshold_averageSensitivity_le_of_nonzero {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x : Cube n, polynomialValue p x ≠ 0) :
    averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by sorry
