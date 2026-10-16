-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Determinant_Euler_aux
-- name    : OAI.ComplexCancellation.Determinant.Euler_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:50:22.088549+00:00
-- url     : https://prove2.me/theorems/f992389d-8857-4747-bd1c-bb7fa1dfceec
-- title:
--   The Euler derivation of $\mathrm{SL}_2\times\mathbb{A}^1$ preserves an auxiliary weight grading
-- statement:
--   Let $T=\mathbb{C}[a,b,c,d,u]/(ac-bd-1)$ be the coordinate ring of $\mathrm{SL}_2\times\mathbb{A}^1$: the classes of $a,b,c,d$ are the entries of the matrix $\begin{pmatrix}a&b\\ d&c\end{pmatrix}$ of determinant $1$, and $u$ is a free coordinate; $T$ is an integral domain. Let $\delta$ and $\eta$ be the $\mathbb{C}$-derivations of $T$ determined by
--
--   $$
--   \delta(a)=\delta(d)=\delta(u)=0,\quad \delta(b)=a,\quad \delta(c)=d;\qquad \eta(b)=\eta(c)=\eta(u)=0,\quad \eta(a)=b,\quad \eta(d)=c,
--   $$
--
--   and let $\theta=[\delta,\eta]=\delta\eta-\eta\delta$ be the Euler derivation, so that $\theta(a)=a$, $\theta(d)=d$, $\theta(b)=-b$, $\theta(c)=-c$ and $\theta(u)=0$. (Geometrically, $\delta$, $\eta$ and $\theta$ generate right multiplication on $\mathrm{SL}_2$ by the upper unipotent, lower unipotent and diagonal subgroups.)
--
--   Give the variables the integer weights $\operatorname{wt}(a)=0$, $\operatorname{wt}(d)=3$, $\operatorname{wt}(b)=-3$, $\operatorname{wt}(c)=0$, $\operatorname{wt}(u)=2$. The relation $ac-bd-1$ is weighted homogeneous of weight $0$, so the images $T_i$ in $T$ of the weighted-homogeneous polynomials of weight $i$ form a $\mathbb{Z}$-grading $T=\bigoplus_{i\in\mathbb{Z}}T_i$ of the $\mathbb{C}$-algebra $T$.
--
--   **Theorem.** The Euler derivation preserves every graded piece of this auxiliary grading:
--
--   $$
--   r\in T_i\ \Longrightarrow\ \theta(r)\in T_i\qquad(i\in\mathbb{Z}).
--   $$
--
--   In other words, $\theta$ is homogeneous of degree $0$ for the auxiliary grading. Consequently $\theta$ commutes with the projections $T\to T_i$, and the homogeneous components of a derivation $E$ with $[\theta,E]=eE$ satisfy the same relation. This is what allows the rigidity argument for $T$ to pass from a locally nilpotent derivation to its highest homogeneous component without losing its Euler weight.
--
--   **Formalization Note** The grading `aux` is `QuotientGrading.pieces` of `weightedHomogeneousSubmodule ℂ ![0, 3, -3, 0, 2]` under the quotient map, with `X 0, …, X 4` standing for $a,d,b,c,u$; it is a `GradedAlgebra` because the kernel of the quotient map is a homogeneous ideal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/DeterminantRigidity.lean#L182-L200

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Determinant
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem OAI.ComplexCancellation.Determinant.Euler_aux {r : T} {i : ℤ} (hr : r ∈ aux i) : Euler r ∈ aux i := by sorry
