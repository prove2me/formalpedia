-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Multigraded_affine_independent_polynomial
-- name    : OAI.PermanentBorder.Multigraded.affine_independent_polynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:27:18.644964+00:00
-- url     : https://prove2.me/theorems/aa2a4b65-2112-4e19-bf92-16e4f6ce874d
-- title:
--   Linear independence persists along a segment away from the roots of a polynomial with $p(0)=1$
-- statement:
--   Let $K$ be a field, $V$ a vector space over $K$, $E$ a finite index set, and let $v=(v_i)_{i\in E}$ and $w=(w_i)_{i\in E}$ be families in $V$ with $v$ linearly independent. Then there is a polynomial $p\in K[t]$ such that $p(0)=1$ and, for every $t\in K$,
--   $$p(t)\neq0\ \Longrightarrow\ \bigl((1-t)\,v_i+t\,w_i\bigr)_{i\in E}\ \text{is linearly independent over}\ K .$$
--
--   Since $p(0)=1$, the polynomial $p$ is nonzero, so linear independence of $v$ persists along the segment from $v$ to $w$ for all but finitely many parameters, the exceptions being among the roots of $p$. No assumption is made on $w$, and $V$ need not be finite-dimensional. Applied to the images of a basis of the range of a linear map, it shows that the rank of $(1-t)f+tg$ is at least the rank of $f$ outside the roots of a polynomial, the semicontinuity step in a deformation argument for counting points.
--
--   **Formalization Note** The polynomial is an element of `Polynomial K`, and the conclusion is `LinearIndependent K (fun i => (1-t) • v i + t • w i)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/LinearForms.lean#L427-L462

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms

open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
variable {K E V : Type*} [Field K] [Fintype E]
  [AddCommGroup V] [Module K V]

theorem OAI.PermanentBorder.Multigraded.affine_independent_polynomial (v w : E → V) (hv : LinearIndependent K v) :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ t : K, p.eval t ≠ 0 →
      LinearIndependent K (fun i => (1-t) • v i + t • w i) := by sorry
