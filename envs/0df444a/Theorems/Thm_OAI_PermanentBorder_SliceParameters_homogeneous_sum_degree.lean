-- Prove2me | Theorems.Thm_OAI_PermanentBorder_SliceParameters_homogeneous_sum_degree
-- name    : OAI.PermanentBorder.SliceParameters.homogeneous_sum_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:57:42.334773+00:00
-- url     : https://prove2.me/theorems/fe1496b0-e4cb-49b6-8296-c1f6130e0708
-- title:
--   A homogeneous polynomial is the sum of its monomials of that degree
-- statement:
--   Let $K$ be a commutative semiring, $\sigma$ a finite set of variables and $d\in\mathbb{Z}$. For an exponent vector $s\in\mathbb{N}^\sigma$ write $|s|=\sum_{j\in\sigma}s_j$, $X^s=\prod_jX_j^{s_j}$, and $f_s$ for the coefficient of $X^s$ in a polynomial $f$. Suppose $f\in K[X_j : j\in\sigma]$ is homogeneous of degree $d$, i.e. $|s|=d$ whenever $f_s\ne0$. Then
--   $$
--   f=\sum_{\substack{s\in\mathbb{N}^\sigma\\ |s|=d}}f_s\,X^s ,
--   $$
--   where the sum runs over the finite set of all exponent vectors of total degree $d$ (it is empty if $d<0$, and then the statement says $f=0$).
--
--   Thus a homogeneous polynomial of degree $d$ is determined by its coefficients on the finitely many monomials of degree $d$, so two homogeneous polynomials of the same degree are equal once these coefficients agree. This identifies homogeneous polynomials of degree $d$ with coefficient vectors indexed by degree-$d$ monomials, which is how Macaulay matrices translate ideal membership in a fixed degree into linear algebra.
--
--   **Formalization Note** Homogeneity is `IsWeightedHomogeneous` for the constant weight $1$ with values in $\mathbb{Z}$, so that degrees such as $D-e_i$ may be negative. The index set of the sum is the type `DegreeIndex σ d` of exponent vectors whose total degree, cast to $\mathbb{Z}$, equals $d$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SmoothSlices.lean#L271-L293

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

theorem OAI.PermanentBorder.SliceParameters.homogeneous_sum_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    {f : MvPolynomial σ K} {d : ℤ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f = ∑ s : DegreeIndex σ d, monomial s.val (f.coeff s.val) := by sorry
