-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_edge_recovery
-- name    : OAI.LeanBlast.GotsmanLinial.edge_recovery
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:56:30.386585+00:00
-- url     : https://prove2.me/theorems/e2487283-3140-4df7-a823-a6f7466d84f6
-- title:
--   Edge recovery: constant-sign cube edges are bounded by the anticommutator energy of a graded matrix
-- statement:
--   Let $Q_n=\{-1,1\}^n$ be the Boolean cube with Hamming distance $d_H$, and write $\|A\|_{\mathrm{HS}}^2=\sum_{x,y}|A_{xy}|^2$ for complex matrices indexed by $Q_n$. Let $M\in\mathbb{C}^{Q_n\times Q_n}$, and let $h:Q_n\to\{-1,1\}$ be a sign function with diagonal matrix $H=\operatorname{diag}(h)$. Assume:
--
--   1. (total energy) $\|M\|_{\mathrm{HS}}^2=\dfrac{n\,2^n}{4}$;
--   2. (distance energy) $\sum_{x,y\in Q_n}d_H(x,y)\,|M_{xy}|^2\le\|M\|_{\mathrm{HS}}^2$;
--   3. (entry cap) $|M_{xy}|^2\le\tfrac14$ for all $x\ne y$.
--
--   Let $E_h=\{(x,y)\in Q_n\times Q_n:\ d_H(x,y)=1,\ h(x)=h(y)\}$ be the set of ordered cube edges along which $h$ is constant. Then
--
--   $$
--   |E_h|\;\le\;2\,\bigl\|MH+HM\bigr\|_{\mathrm{HS}}^2 .
--   $$
--
--   This is the combinatorial core of the edge-counting step in the Gotsman–Linial argument. There $M$ is the centred degree grading $\sum_k\bigl(k-\tfrac n2\bigr)P_k$ of an orthogonal decomposition with binomial multiplicities, and $h$ is the threshold function multiplied by the full parity, whose constant edges are exactly the sensitive edges of the threshold function. Together with an upper bound on the anticommutator energy, it bounds the average sensitivity.
--
--   **Formalization Note** Vertices are Boolean vectors `Cube n`; $h$ is a real function taking only the values $1$ and $-1$, and $H$ is the complex diagonal matrix with entries $h(x)$. The set $E_h$ is `orderedConstantEdges h`, the subset of the ordered pairs at Hamming distance one (`orderedNeighborPairs n`) on which $h$ takes equal values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean#L173-L197

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

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators
variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem OAI.LeanBlast.GotsmanLinial.edge_recovery {n : ℕ} (M : Matrix (Cube n) (Cube n) ℂ)
    (h : Cube n → ℝ) (hh : ∀ x, h x = 1 ∨ h x = -1)
    (htotal : hsNormSq M = (n : ℝ) * (2 : ℝ) ^ n / 4)
    (hdistance : (∑ x, ∑ y, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤ hsNormSq M)
    (hcap : ∀ x y, x ≠ y → ‖M x y‖ ^ 2 ≤ (1 / 4 : ℝ)) :
    ((orderedConstantEdges h).card : ℝ) ≤
      2 * hsNormSq (M * Matrix.diagonal (fun x => (h x : ℂ)) +
        Matrix.diagonal (fun x => (h x : ℂ)) * M) := by sorry
