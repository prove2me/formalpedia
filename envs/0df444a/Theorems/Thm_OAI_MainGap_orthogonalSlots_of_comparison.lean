-- Prove2me | Theorems.Thm_OAI_MainGap_orthogonalSlots_of_comparison
-- name    : OAI.MainGap.orthogonalSlots_of_comparison
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:17:09.3663+00:00
-- url     : https://prove2.me/theorems/b4322209-cb5d-4ad1-932a-1c2aafe07c34
-- title:
--   A Cuntz comparison $\operatorname{diag}_n(d)\precsim v$ yields $n$ orthogonal slots for $(d-\varepsilon)_+$ into $\operatorname{Her}(v)$
-- statement:
--   Let $A$ be a C*-algebra (not necessarily unital) with its usual order. We use the following notation.
--
--   - $\operatorname{Her}(x)=\overline{xAx^*}$ is the norm closure of $\{xax^*: a\in A\}$, a closed $*$-subalgebra of $A$.
--   - For self-adjoint $d$ and $\varepsilon\in\mathbb{R}$, $(d-\varepsilon)_+=f_\varepsilon(d)$ with $f_\varepsilon(t)=\max(t-\varepsilon,0)$ (continuous functional calculus).
--   - For $d\in M_n(A)$ and $v\in M_m(A)$, $d\precsim v$ means that there are $r_j\in M_{m\times n}(A)$ with $r_j^*vr_j\to d$ in norm; $\operatorname{diag}_n(d)\in M_n(A)$ is the diagonal matrix with all diagonal entries $d$, and $(v)\in M_1(A)$ is the $1\times1$ matrix with entry $v$.
--   - For $h,v\in A$ and $n\in\mathbb{N}$, a family of *$n$ orthogonal slots for $h$ into $v$* is a family $S_1,\dots,S_n$ of bounded $\mathbb{C}$-linear maps $\operatorname{Her}(h)\to A$ such that for all $i,j$ and all $k,l\in\operatorname{Her}(h)$
--   $$S_i(k)^*S_j(l)=\delta_{ij}\,k^*l,\qquad S_i(k)\,S_j(l)^*\in\operatorname{Her}(v),\qquad S_i(kl)=S_i(k)\,l.$$
--
--   **Theorem.** Let $d,v\in A$ be positive and $n\in\mathbb{N}$, and assume $\operatorname{diag}_n(d)\precsim(v)$, i.e. there are rows $(r_{j,1},\dots,r_{j,n})$ with $r_{j,p}^*\,v\,r_{j,q}\to\delta_{pq}\,d$ for all $p,q$. Then for every $\varepsilon>0$ there exists a family of $n$ orthogonal slots for $(d-\varepsilon)_+$ into $v$.
--
--   Each slot $S_i$ is isometric ($\|S_i(k)\|^2=\|k^*k\|=\|k\|^2$) and right $\operatorname{Her}((d-\varepsilon)_+)$-linear, different slots have orthogonal ranges in the sense $S_i(k)^*S_j(l)=0$ for $i\neq j$, and all products $S_i(k)S_j(l)^*$ land in $\operatorname{Her}(v)$. Thus a Cuntz comparison provides $n$ orthogonal copies of $\operatorname{Her}((d-\varepsilon)_+)$ placed under $v$; this is the device used to choose pairs of orthogonal contractions in the subsequent construction.
--
--   **Formalization Note** The conclusion is `Nonempty (OrthogonalSlots n (cut d ε) v)`, where `cut d ε` is $(d-\varepsilon)_+$ and the slots are indexed by `Fin n`. The case $n=0$ is allowed (the empty family). The order on $A$ is `CStarAlgebra.spectralOrder`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/OrthogonalSlots.lean#L313-L329

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass
variable {A : Type*} [NonUnitalCStarAlgebra A]
open scoped CStarAlgebra

theorem OAI.MainGap.orthogonalSlots_of_comparison {n : ℕ} {d v : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hdv : FiniteCuntzLE (diagonalCorner n d) (scalarCorner v)) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (OrthogonalSlots n (cut d ε) v) := by sorry
