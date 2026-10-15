-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_weightedFlag_block_eq_zero_of_polynomial_degree
-- name    : OAI.LeanBlast.GotsmanLinial.weightedFlag_block_eq_zero_of_polynomial_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:58:37.89409+00:00
-- url     : https://prove2.me/theorems/9007c62d-8615-4fae-8858-9740f6a04837
-- title:
--   Low antidiagonal blocks of the parity-twisted polynomial threshold vanish in the weighted Walsh grading
-- statement:
--   Identify the Boolean cube with $\{-1,1\}^n$ and write $x_i \in \{-1,1\}$ for the coordinates of a vertex $x$. Let $\mathcal{H} = \mathbb{C}^{\{-1,1\}^n}$ carry the counting inner product $\langle f, g\rangle = \sum_x \overline{f(x)}\,g(x)$. For $S \subseteq \{1,\dots,n\}$ let $\chi_S(x) = \prod_{i\in S} x_i$ be the Walsh character, let $\mathcal{F}_{\le k} = \operatorname{span}_{\mathbb{C}}\{\chi_S : |S| \le k\}$ be the space of functions of Fourier degree at most $k$, and write $\chi = \chi_{\{1,\dots,n\}}$ for the full parity $\chi(x) = \prod_{i=1}^n x_i$. The threshold sign is $\operatorname{sgn}(t) = 1$ for $t \ge 0$ and $\operatorname{sgn}(t) = -1$ for $t < 0$.
--
--   Let $n, d, r, s$ be natural numbers and let $p \in \mathbb{R}[X_1,\dots,X_n]$ be multilinear (every monomial in its support has exponent at most $1$ in each variable) with total degree at most $d$. Assume $p(x) \neq 0$ for every $x \in \{-1,1\}^n$, and put $w(x) = |p(x)| > 0$. Define the weighted Fourier flag
--   $$
--   K_0 = \{0\}, \qquad K_{k+1} = \sqrt{w}\cdot\mathcal{F}_{\le k} = \{\sqrt{w}\,f : f \in \mathcal{F}_{\le k}\} \quad (k \ge 0),
--   $$
--   let $\Pi_k$ be the orthogonal projection of $\mathcal{H}$ onto the layer $L_k = K_{k+1} \cap K_k^{\perp}$, and let $H$ be the multiplication operator $(Hf)(x) = \chi(x)\,\operatorname{sgn}(p(x))\,f(x)$. If $r + s < n - d$, then
--
--   $$
--   \Pi_s \, H \, \Pi_r = 0 .
--   $$
--
--   The layers $L_0, \dots, L_n$ form the orthogonal grading of $\mathcal{H}$ attached to $p$ in the matrix proof of the Gotsman–Linial theorem. This statement is the only place where the degree bound on $p$ enters that proof: it says that the parity-twisted threshold function has no matrix blocks strictly below the antidiagonal $r + s = n - d$, which is what the block-coupling estimate for the anticommutator energy consumes.
--
--   **Formalization Note** The difference $n - d$ is truncated subtraction of natural numbers, so for $d \ge n$ the hypothesis $r + s < n - d$ cannot hold and the statement is vacuous. The flag is `weightedFourierFlag` applied to `fun x => |polynomialValue p x|` (with positivity derived from the non-vanishing hypothesis), $\Pi_k$ is `flagProjection K k`, i.e. the `starProjection` onto `flagLayer K k`, and $H$ is `signMultiplier` of `fun x => fullParity x * thresholdSign (polynomialValue p x)`; the product is composition of continuous linear operators on `EuclideanSpace ℂ (Cube n)`. Cube vertices are `Fin n → Bool` with `true` read as $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/BlockVanishing.lean#L186-L207

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
open scoped BigOperators ComplexConjugate

theorem OAI.LeanBlast.GotsmanLinial.weightedFlag_block_eq_zero_of_polynomial_degree
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0) (hrs : r + s < n - d) :
    let K := weightedFourierFlag (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    flagProjection K s *
      signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) *
        flagProjection K r = 0 := by sorry
