-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sum_mul_eq_zero_of_fourier_separated
-- name    : OAI.LeanBlast.GotsmanLinial.sum_mul_eq_zero_of_fourier_separated
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:52:21.657459+00:00
-- url     : https://prove2.me/theorems/b0ffce9f-06d7-4754-bb01-4ef2c035b42f
-- title:
--   Functions with separated Walsh supports have zero counting pairing
-- statement:
--   Let $\chi_S(x)=\prod_{i\in S}x_i$ be the complex-valued Walsh characters on $\{-1,1\}^n$, and let $\mathcal V_r=\operatorname{span}_{\mathbb{C}}\{\chi_S:|S|\le r\}$ and $\mathcal W_s=\operatorname{span}_{\mathbb{C}}\{\chi_S:|S|\ge s\}$. If $r<s$, $a\in\mathcal V_r$ and $b\in\mathcal W_s$, then
--
--   $$
--   \sum_{x\in\{-1,1\}^n}a(x)\,b(x)=0 .
--   $$
--
--   No complex conjugation appears: since the Walsh characters are real, already the bilinear pairing $\sum_xa(x)b(x)$ vanishes between functions of Fourier degree at most $r$ and functions supported on degrees at least $s>r$. This orthogonality is what makes the low blocks of the parity-twisted sign matrix vanish in the Gotsman–Linial argument, and it also shows that all low Walsh coefficients of a parity-twisted low-degree polynomial are zero.
--
--   **Formalization Note** $\mathcal V_r$ is `fourierSpace n r` and $\mathcal W_s$ is `fourierSpaceFrom n s`; the sum runs over all $2^n$ points of `Cube n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/PolynomialDegree.lean#L198-L225

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

theorem OAI.LeanBlast.GotsmanLinial.sum_mul_eq_zero_of_fourier_separated {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpaceFrom n s) (hrs : r < s) :
    (∑ x : Cube n, a x * b x) = 0 := by sorry
