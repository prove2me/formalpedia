-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Polar_rows_independent_of_derivations
-- name    : OAI.PermanentBorder.Polar.rows_independent_of_derivations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:04:13.032219+00:00
-- url     : https://prove2.me/theorems/0a793f4e-f454-4612-851b-6848f13606c5
-- title:
--   Derivations in generic parameters make the gradient, polar gradients and a linear form independent
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $\sigma,\tau$ be finite sets. Let $f\in K[X_j : j\in\sigma]$, a point $y\in L^\sigma$, directions $w=(w_{ij})_{i\in\tau,\,j\in\sigma}$ with entries in $L$, and $l\in L^\sigma$. Write $\partial_jf(y)$ for the partial derivatives of $f$ evaluated at $y$ (through $K\to L$), and
--   $$
--   \Pi_i(y)=\sum_{j\in\sigma}w_{ij}\,\partial_jf(y),\qquad G_{ij}=\sum_{k\in\sigma}w_{ik}\,\partial_j\partial_kf(y)\qquad(i\in\tau,\ j\in\sigma)
--   $$
--   for the polar values and the polar gradients. Let $\tau_\ast=\{\ast\}\sqcup\tau$, and let $(D_{a,b})_{(a,b)\in\tau_\ast\times\sigma}$ be $K$-linear derivations of $L$ that act like partial derivatives with respect to the entries of $w$ and $l$:
--   $$
--   D_{a,b}(w_{ij})=[\,(a,b)=(i,j)\,],\qquad D_{a,b}(l_j)=[\,(a,b)=(\ast,j)\,],
--   $$
--   where $[P]$ is $1$ if $P$ holds and $0$ otherwise. Assume
--   1. $f(y)=0$ and $\Pi_i(y)=0$ for every $i\in\tau$;
--   2. $\sum_{j}l_jy_j=0$ or $\sum_jl_jy_j=1$;
--   3. $y\ne0$, and $\partial_jf(y)\ne0$ for some $j\in\sigma$.
--
--   Then the gradient $\nabla f(y)$, the polar gradients $(G_{ij})_{j\in\sigma}$ for $i\in\tau$, and the vector $l$ are linearly independent over $L$. That is, whenever $c,z\in L$ and $\gamma\in L^\tau$ satisfy
--   $$
--   c\,\partial_jf(y)+\sum_{i\in\tau}\gamma_i\,G_{ij}+z\,l_j=0\qquad\text{for all } j\in\sigma,
--   $$
--   then $c=0$, $z=0$ and $\gamma=0$.
--
--   The derivations exist when the entries of $w$ and $l$ are independent indeterminates (for instance in an algebraic closure of a rational function field in characteristic zero). In that case the theorem is a transversality statement. At a nonzero point of the hypersurface $f=0$ where the gradient does not vanish and all generic polars vanish, and which lies on the hyperplane $\sum_jl_jy_j=0$ or on the affine chart $\sum_jl_jy_j=1$, the defining equations meet transversally. It is the key step in showing that a smooth hypersurface cut by generic polars has only nondegenerate intersection points, none of them at infinity.
--
--   **Formalization Note** The derivations are a family `D : Option τ × σ → Derivation K L L`, with the index $\ast$ being `none`. The condition $y\ne0$ is stated as the existence of a nonzero coordinate, and polynomials over $K$ are evaluated at $y$ with `aeval`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/GenericPolars.lean#L79-L147

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

open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open MvPolynomial
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype σ] [Fintype τ]

theorem OAI.PermanentBorder.Polar.rows_independent_of_derivations [DecidableEq τ] [DecidableEq σ]
    (w : τ → σ → L) (l : σ → L) (f : MvPolynomial σ K) (y : σ → L)
    (D : Option τ × σ → Derivation K L L)
    (hw : ∀ a b i j, D (a,b) (w i j) = if (a,b) = (some i,j) then 1 else 0)
    (hl : ∀ a b j, D (a,b) (l j) = if (a,b) = (none,j) then 1 else 0)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue w f y i = 0)
    (hn : ∑ j, l j * y j = 0 ∨ ∑ j, l j * y j = 1)
    (hy : ∃ j, y j ≠ 0) (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (c z : L) (cfs : τ → L)
    (hdep : ∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j + z * l j = 0) :
    c = 0 ∧ z = 0 ∧ cfs = 0 := by sorry
