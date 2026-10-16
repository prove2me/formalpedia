-- Prove2me | Theorems.Thm_OAI_PermanentBorder_SliceParameters_homogeneous_piece_certificate
-- name    : OAI.PermanentBorder.SliceParameters.homogeneous_piece_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:56:49.318005+00:00
-- url     : https://prove2.me/theorems/407a1c65-955b-49a6-97c5-1be53e9f92da
-- title:
--   An ideal whose only zero is the origin contains all homogeneous polynomials of some degree
-- statement:
--   Let $K$ be a field, $L$ an algebraically closed field that is a $K$-algebra, $\sigma$ a finite set of variables and $I$ an ideal of $K[X_j : j\in\sigma]$. Polynomials with coefficients in $K$ are evaluated at points of $L^\sigma$ through the structure map $K\to L$, and
--   $$
--   Z_L(I)=\{y\in L^\sigma : p(y)=0\ \text{for all } p\in I\}
--   $$
--   denotes the zero locus of $I$ in $L^\sigma$. If the origin is the only possible point of this zero locus, i.e. $Z_L(I)\subseteq\{0\}$, then there is a degree $D\in\mathbb{N}$ such that every homogeneous polynomial of degree $D$ lies in $I$:
--   $$
--   \exists\,D\in\mathbb{N}\quad\forall f\in K[X_j : j\in\sigma]:\qquad f\ \text{homogeneous of degree } D\ \Longrightarrow\ f\in I .
--   $$
--
--   This is an effective form of the projective Nullstellensatz. A system of homogeneous polynomials with no nontrivial common zero over an algebraically closed field has no projective zeros, and the theorem provides a degree $D$ in which the ideal is everything. Such a degree certifies the absence of projective zeros by a linear-algebra condition, namely surjectivity of the degree-$D$ Macaulay matrix.
--
--   **Formalization Note** $Z_L(I)$ is Mathlib's `MvPolynomial.zeroLocus L I`. Homogeneity is `IsHomogeneous D`, which also holds for the zero polynomial.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SmoothSlices.lean#L213-L228

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

open OAI OAI.PermanentBorder OAI.PermanentBorder.SliceParameters
open MvPolynomial

theorem OAI.PermanentBorder.SliceParameters.homogeneous_piece_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) :
    ∃ D : ℕ, ∀ f : MvPolynomial σ K, f.IsHomogeneous D → f ∈ I := by sorry
