-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_parity_mul_mem_fourierSpaceFrom
-- name    : OAI.LeanBlast.GotsmanLinial.parity_mul_mem_fourierSpaceFrom
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:51:32.633605+00:00
-- url     : https://prove2.me/theorems/8dcf1964-8eb4-4ce8-b879-42e4a9aefcf2
-- title:
--   Multiplication by the full parity sends Fourier degree at most $d$ to Walsh support in degrees at least $n-d$
-- statement:
--   Let $\chi_S(x)=\prod_{i\in S}x_i$ be the complex-valued Walsh characters on $\{-1,1\}^n$. Let $\mathcal V_d=\operatorname{span}_{\mathbb{C}}\{\chi_S:|S|\le d\}$ (Fourier degree at most $d$) and $\mathcal W_k=\operatorname{span}_{\mathbb{C}}\{\chi_S:|S|\ge k\}$ (Walsh support in degrees at least $k$), and let $\chi_{[n]}(x)=\prod_{i=1}^{n}x_i$ be the full parity. For every $a:\{-1,1\}^n\to\mathbb{C}$,
--
--   $$
--   a\in\mathcal V_d\ \Longrightarrow\ \bigl(x\mapsto\chi_{[n]}(x)\,a(x)\bigr)\in\mathcal W_{n-d},
--   $$
--
--   where $n-d$ is truncated at $0$; for $d\ge n$ the conclusion is membership in $\mathcal W_0$, the whole function space.
--
--   Multiplication by the parity complements index sets, $\chi_{[n]}\chi_S=\chi_{[n]\setminus S}$, so low-degree functions become functions supported on high degrees. In the Gotsman–Linial argument the threshold sign is twisted by the parity, and this lemma, together with orthogonality of low and high Walsh levels, yields the vanishing of the low antidiagonal blocks.
--
--   **Formalization Note** $\mathcal V_d$ is `fourierSpace n d`, $\mathcal W_k$ is `fourierSpaceFrom n k`, the full parity is `walshChar Finset.univ`, and `n - d` is natural-number subtraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean#L176-L196

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

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators symmDiff
variable {n d : ℕ}

theorem OAI.LeanBlast.GotsmanLinial.parity_mul_mem_fourierSpaceFrom {a : Cube n → ℂ}
    (ha : a ∈ fourierSpace n d) :
    (fun x => walshChar Finset.univ x * a x) ∈ fourierSpaceFrom n (n - d) := by sorry
