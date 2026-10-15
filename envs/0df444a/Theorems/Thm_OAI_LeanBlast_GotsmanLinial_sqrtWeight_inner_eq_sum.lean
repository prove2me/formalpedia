-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sqrtWeight_inner_eq_sum
-- name    : OAI.LeanBlast.GotsmanLinial.sqrtWeight_inner_eq_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:57:16.593905+00:00
-- url     : https://prove2.me/theorems/daf79cd2-0275-4469-b14c-f9c36d1af251
-- title:
--   Pairing of square-root-weighted vectors through a diagonal multiplier
-- statement:
--   Let $\Omega$ be a finite set and equip $\mathbb{C}^{\Omega}$ with the counting inner product $\langle u, v\rangle = \sum_{x\in\Omega} \overline{u(x)}\, v(x)$, which is conjugate-linear in the first argument. Let $w, h : \Omega \to \mathbb{R}$ be real functions with $w(x) \ge 0$ for every $x \in \Omega$. Let $D$ be a $\mathbb{C}$-linear operator on $\mathbb{C}^{\Omega}$ acting as multiplication by $\sqrt{w}$, that is $(Da)(x) = \sqrt{w(x)}\, a(x)$ for all $a$ and $x$, and let $H$ be a continuous $\mathbb{C}$-linear operator acting as multiplication by $h$, that is $(Ha)(x) = h(x)\, a(x)$. Then for all $a, b \in \mathbb{C}^{\Omega}$,
--
--   $$
--   \langle D b,\; H(D a)\rangle \;=\; \sum_{x\in\Omega} \overline{b(x)}\, a(x)\, w(x)\, h(x).
--   $$
--
--   Thus a matrix coefficient of a diagonal operator between two subspaces that have been transported by the square-root weight $\sqrt{w}$ becomes an unweighted finite sum against the signed weight $w h$. This is the computation that turns block-vanishing questions for weighted gradings into Fourier orthogonality statements; in the Gotsman–Linial argument it is used with $w = |p|$ and $h = \chi \cdot \operatorname{sgn}(p)$, where $p$ is a polynomial and $\chi$ the full parity.
--
--   **Formalization Note** The Hilbert space is `EuclideanSpace ℂ Ω`; $D$ is only assumed to be a linear map and $H$ a continuous linear map, each specified through its pointwise formula. The hypothesis $w \ge 0$ is what makes $\sqrt{w(x)}^2 = w(x)$ (Lean's `Real.sqrt` is $0$ on negative inputs).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/BlockVanishing.lean#L63-L87

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

theorem OAI.LeanBlast.GotsmanLinial.sqrtWeight_inner_eq_sum
    {Ω : Type*} [Fintype Ω]
    (w h : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (D : EuclideanSpace ℂ Ω →ₗ[ℂ] EuclideanSpace ℂ Ω)
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ Ω →L[ℂ] EuclideanSpace ℂ Ω)
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ Ω) :
    inner ℂ (D b) (H (D a)) =
      ∑ x, star (b x) * a x * ((w x : ℂ) * (h x : ℂ)) := by sorry
