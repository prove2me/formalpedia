-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_finite_one_sided_coupling_bound
-- name    : OAI.LeanBlast.GotsmanLinial.finite_one_sided_coupling_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:41:06.198549+00:00
-- url     : https://prove2.me/theorems/1b3c8321-2176-4cc2-8c40-f7fc7565ab4f
-- title:
--   One-sided coupling bound: equal distributions and $V-U\le a$ give $\mathbb{E}(U-V)^2\le 8a\sigma$
-- statement:
--   Let $\Omega$ be a finite set carrying probability weights $w:\Omega\to\mathbb{R}$, that is, $w(i)\ge 0$ for every $i\in\Omega$ and $\sum_{i\in\Omega}w(i)=1$, and write $\mathbb{E}[F]=\sum_{i\in\Omega}w(i)\,F(i)$ for a real function $F$ on $\Omega$. Let $U,V:\Omega\to\mathbb{R}$ and $m,\sigma,a\in\mathbb{R}$, and assume:
--
--   1. ($U$ and $V$ are equally distributed) $\mathbb{E}[\varphi(U)]=\mathbb{E}[\varphi(V)]$ for every function $\varphi:\mathbb{R}\to\mathbb{R}$;
--   2. $\sigma\ge 0$ and $a\ge 0$;
--   3. the second moment of $U$ about the centre $m$ equals $\sigma^2$: $\mathbb{E}[(U-m)^2]=\sigma^2$;
--   4. (one-sided increment bound) $V(i)-U(i)\le a$ for every $i$ with $w(i)\ne 0$.
--
--   Then
--
--   $$
--   \sum_{i\in\Omega}w(i)\,\bigl(U(i)-V(i)\bigr)^2\;\le\;8\,a\,\sigma .
--   $$
--
--   In words: if two equally distributed random variables are coupled so that $V$ never exceeds $U$ by more than $a$, their mean squared displacement is at most $8a\sigma$, where $\sigma$ measures the spread of the common law. Only a one-sided bound on $V-U$ is required, because equality of the distributions forces downward moves to be balanced by upward ones. The centre $m$ is arbitrary; taking $m=\mathbb{E}[U]$ makes $\sigma^2$ the variance. In the Gotsman–Linial argument this estimate is applied to a coupling of two symmetric binomial variables.
--
--   **Formalization Note** $\Omega$ is a `Fintype` and expectations are finite weighted sums, so equality of distributions is expressed as equality of the weighted sums of $\varphi\circ U$ and $\varphi\circ V$ for every function $\varphi$, with no measurability conditions. The increment hypothesis is imposed only on the support of $w$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/FiniteCoupling.lean#L64-L123

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

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω]

theorem OAI.LeanBlast.GotsmanLinial.finite_one_sided_coupling_bound (w U V : Ω → ℝ) (m σ a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (hσ : 0 ≤ σ) (ha : 0 ≤ a)
    (hvariance : ∑ i, w i * (U i - m) ^ 2 = σ ^ 2)
    (hstep : ∀ i, w i ≠ 0 → V i - U i ≤ a) :
    ∑ i, w i * (U i - V i) ^ 2 ≤ 8 * a * σ := by sorry
