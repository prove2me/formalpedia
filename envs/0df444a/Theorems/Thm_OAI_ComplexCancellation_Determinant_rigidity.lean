-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Determinant_rigidity
-- name    : OAI.ComplexCancellation.Determinant.rigidity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:50:50.974579+00:00
-- url     : https://prove2.me/theorems/f1fc42a8-da92-45b1-b715-a22e6482a235
-- title:
--   Rigidity of $\mathrm{SL}_2\times\mathbb{A}^1$: a locally nilpotent derivation of Euler weight $e\le 0$ with $E^2(v)=0$ vanishes
-- statement:
--   Let $T=\mathbb{C}[a,b,c,d,u]/(ac-bd-1)$ be the coordinate ring of $\mathrm{SL}_2\times\mathbb{A}^1$: the classes of $a,b,c,d$ are the entries of the matrix $\begin{pmatrix}a&b\\ d&c\end{pmatrix}$ of determinant $1$, and $u$ is a free coordinate; $T$ is an integral domain. Let $\delta$ and $\eta$ be the $\mathbb{C}$-derivations of $T$ determined by
--
--   $$
--   \delta(a)=\delta(d)=\delta(u)=0,\quad \delta(b)=a,\quad \delta(c)=d;\qquad \eta(b)=\eta(c)=\eta(u)=0,\quad \eta(a)=b,\quad \eta(d)=c,
--   $$
--
--   and let $\theta=[\delta,\eta]=\delta\eta-\eta\delta$ be the Euler derivation, so that $\theta(a)=a$, $\theta(d)=d$, $\theta(b)=-b$, $\theta(c)=-c$ and $\theta(u)=0$. (Geometrically, $\delta$, $\eta$ and $\theta$ generate right multiplication on $\mathrm{SL}_2$ by the upper unipotent, lower unipotent and diagonal subgroups.) Finally put $v=a^3b-a^2u^3-d^2\in T$; it is homogeneous of Euler weight $2$, i.e. $\theta(v)=2v$.
--
--   **Theorem.** Let $E$ be a locally nilpotent $\mathbb{C}$-derivation of $T$ (every $r\in T$ satisfies $E^n(r)=0$ for some $n\in\mathbb{N}$) and let $e\in\mathbb{Z}$ with $e\le0$. If $E$ shifts Euler weights by $e$ and $E$ applied twice kills $v$, then $E=0$:
--
--   $$
--   \Bigl(\theta\bigl(E(r)\bigr)-E\bigl(\theta(r)\bigr)=e\,E(r)\ \text{ for all } r\in T\Bigr)\ \text{ and }\ E\bigl(E(v)\bigr)=0\quad\Longrightarrow\quad E=0 .
--   $$
--
--   This is the rigidity input of an obstruction argument for an auxiliary ring obtained from $T$ by an affine modification along $v$: a nonzero locally nilpotent derivation there, with suitable homogeneity, is reduced to a derivation $E$ of $T$ satisfying the hypotheses above with $e=-n\le0$, and the theorem shows that such an $E$ must vanish.
--
--   **Formalization Note** $T$ is `MvPolynomial (Fin 5) ℂ ⧸ (X 0 * X 3 - X 2 * X 1 - 1)` with $a,d,b,c,u$ the classes of `X 0, …, X 4`; $\theta$ is `Euler = ⁅δ, η⁆`, the weight condition is `FiberShift E e`, and local nilpotence is `LND.LocallyNilpotent E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/DeterminantRigidity.lean#L250-L271

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

theorem OAI.ComplexCancellation.Determinant.rigidity (E : Derivation ℂ T T) (hln : LND.LocallyNilpotent E)
    (e : ℤ) (he : e ≤ 0) (hshift : FiberShift E e) (hv : E (E v) = 0) : E = 0 := by sorry
