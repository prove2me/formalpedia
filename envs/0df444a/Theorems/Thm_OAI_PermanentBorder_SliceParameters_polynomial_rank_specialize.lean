-- Prove2me | Theorems.Thm_OAI_PermanentBorder_SliceParameters_polynomial_rank_specialize
-- name    : OAI.PermanentBorder.SliceParameters.polynomial_rank_specialize
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:11:19.834117+00:00
-- url     : https://prove2.me/theorems/17a354a2-0ca2-4658-b1b6-fef756a23eec
-- title:
--   Full row rank of a polynomial matrix at a point over an extension field specializes to a point over an infinite base field
-- statement:
--   Let $K$ be an infinite field and $L$ a field that is a $K$-algebra. Let $\alpha,\beta$ be finite index sets and $\sigma$ an arbitrary set of variables. Let $P=(P_{ab})_{a\in\alpha,\,b\in\beta}$ be a matrix with entries in the polynomial ring $K[X_s : s\in\sigma]$. For a point $x\in L^\sigma$, let $P(x)$ be the $\alpha\times\beta$ matrix over $L$ obtained by evaluating every entry at $x$ (coefficients mapped into $L$), and similarly $P(y)$ for $y\in K^\sigma$. If the linear map $L^\beta\to L^\alpha$, $v\mapsto P(x)v$, is surjective for some $x\in L^\sigma$, then
--   $$
--   \exists\,y\in K^\sigma:\qquad v\mapsto P(y)\,v\ \ \text{is a surjection } K^\beta\to K^\alpha .
--   $$
--
--   In words, if a polynomial matrix has full row rank at some point over an extension field, it already has full row rank at some point with coordinates in the infinite base field. This lets a rank condition proved at a generic point (in a large transcendental extension) be realized by concrete parameter values. It is used to choose explicit complex directions and linear forms for which the Macaulay matrix of a polar system remains surjective.
--
--   **Formalization Note** Evaluation at $x$ is `eval₂Hom (algebraMap K L) x` applied entrywise with `Matrix.map`, and surjectivity is stated for `mulVec`. No finiteness is assumed on $\sigma$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/RankTransfer.lean#L82-L134

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer

open OAI OAI.PermanentBorder OAI.PermanentBorder.SliceParameters
open MvPolynomial

theorem OAI.PermanentBorder.SliceParameters.polynomial_rank_specialize {K L σ α β : Type*}
    [Field K] [Field L] [Algebra K L] [Infinite K] [Fintype α] [Fintype β]
    (P : Matrix α β (MvPolynomial σ K)) (x : σ → L)
    (hP : Function.Surjective (P.map (eval₂Hom (algebraMap K L) x)).mulVec) :
    ∃ y : σ → K,
      Function.Surjective (P.map (eval₂Hom (RingHom.id K) y)).mulVec := by sorry
