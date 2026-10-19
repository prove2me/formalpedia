-- Prove2me | Theorems.Thm_OAI_MainGap_individual_to_strong
-- name    : OAI.MainGap.individual_to_strong
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:58:18.661401+00:00
-- url     : https://prove2.me/theorems/04a76c99-5303-418d-bcdf-b0bc1222e24b
-- title:
--   Property P implies unrestricted diagonalization: $s^*as\approx a$, $t^*bt\approx b$ and $s^*ct\approx0$ for positive $a,b$ and any $c$
-- statement:
--   Let $A$ be a C*-algebra, possibly non-unital, with its usual order: $x\le y$ means that $y-x$ is positive (self-adjoint with spectrum in $[0,\infty)$). For $m,n\in\mathbb{N}$ write $M_{m,n}(A)$ for the $m\times n$ matrices over $A$ and $M_n(A)=M_{n,n}(A)$ for the C*-algebra of $n\times n$ matrices; $r^*$ denotes the conjugate transpose of a matrix $r$.
--
--   We say that $A$ has *Property P* if every positive $h\in A$ is properly infinite in the following matricial sense: there is a sequence of rows $r_j=(x_j\ \ y_j)\in M_{1,2}(A)$, $j\in\mathbb{N}$, such that
--   $$r_j^*\,h\,r_j=\begin{pmatrix}x_j^*hx_j&x_j^*hy_j\\ y_j^*hx_j&y_j^*hy_j\end{pmatrix}\longrightarrow\begin{pmatrix}h&0\\0&h\end{pmatrix}\qquad\text{in }M_2(A)\text{ as }j\to\infty .$$
--
--   **Theorem.** If $A$ has Property P, then for all positive $a,b\in A$, every $c\in A$ and every real $\varepsilon>0$ there exist $s,t\in A$ with
--   $$\|s^*as-a\|<\varepsilon,\qquad\|t^*bt-b\|<\varepsilon,\qquad\|s^*ct\|<\varepsilon .$$
--
--   The conclusion is an *unrestricted diagonalization* property: any two positive elements can be approximately reproduced by conjugations $y\mapsto s^*ys$ and $y\mapsto t^*yt$ that are, at the same time, almost orthogonal with respect to a prescribed third element $c$. Specializing to $a=x^2$, $b=y^2$ and $c=xy$ for positive $x,y$ gives the defining condition of strong pure infiniteness. Thus Property P, a condition on each positive element separately, implies this simultaneous two-element condition.
--
--   **Formalization Note** The conclusion is `UnrestrictedDiagonalization A`, i.e. `∀ a b : A, 0 ≤ a → 0 ≤ b → ∀ c : A, ∀ ε : ℝ, 0 < ε → Diagonalization a b c ε`, where `Diagonalization a b c ε` is the existence of $s,t$ with the three displayed estimates. Property P is `PropertyP A` from the comparison module, `∀ h, 0 ≤ h → FiniteCuntzLE (doubleCorner h) (scalarCorner h)`, with rows of type `CStarMatrix (Fin 1) (Fin 2) A`; convergence is in the topology of `CStarMatrix`, which is the entrywise one. This is the finite-matrix form of Property P, as opposed to the form in the stabilization used in the main theorem. Positivity refers to the spectral order, installed by local instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Diagonalization.lean#L66-L94

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Separation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealDetection
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_IdealComparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Signal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Diagonalization

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.diagonalizationPartialOrder
attribute [local instance] OAI.MainGap.diagonalizationStarOrderedRing
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.individual_to_strong (hP : PropertyP A) : UnrestrictedDiagonalization A := by sorry
