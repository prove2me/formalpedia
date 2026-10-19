-- Prove2me | Theorems.Thm_OAI_MainGap_RegularTransport_carrier_entryHer
-- name    : OAI.MainGap.RegularTransport.carrier_entryHer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:16:41.16972+00:00
-- url     : https://prove2.me/theorems/55b75804-515a-40d5-ab48-468b1bc3df2e
-- title:
--   A regular transport into a matrix corner sends column matrix units into that corner
-- statement:
--   Let $C$ be a C*-algebra and $x,y\in C$, and write $\operatorname{Her}(x)=\overline{xCx^*}$ (norm closure), a closed $*$-subalgebra of $C$. A *regular transport* from $x$ to $y$ is a pair $(\Phi,\theta)$ consisting of a bounded $\mathbb{C}$-linear map $\Phi:\operatorname{Her}(x)\to C$ and a $*$-homomorphism $\theta:\operatorname{Her}(x)\to C$ such that for all $k,l\in\operatorname{Her}(x)$
--
--   $$
--   \Phi(k)^*\Phi(l)=k^*l,\qquad \Phi(k)\Phi(l)^*=\theta(kl^*),\qquad \Phi(kl)=\Phi(k)\,l,\qquad \theta(k)\in\operatorname{Her}(y).
--   $$
--
--   Now let $A$ be a C*-algebra (not necessarily unital), $n\in\mathbb{N}$, $h,v\in A$ and $i_0\in\{1,\dots,n\}$. In $M_n(A)$ write $E_{jk}(a)$ for the matrix with $a$ in entry $(j,k)$ and zeros elsewhere, and $\operatorname{diag}_n(h)$ for the diagonal matrix with all diagonal entries equal to $h$. Let $(\Phi,\theta)$ be a regular transport in $C=M_n(A)$ from $\operatorname{diag}_n(h)$ to $E_{i_0i_0}(v)$. For $k\in\operatorname{Her}(h)$ and every index $i$, the matrix $E_{ii_0}(k)$ belongs to $\operatorname{Her}(\operatorname{diag}_n(h))$, so $\Phi$ can be applied to it.
--
--   **Theorem.** For every $i\in\{1,\dots,n\}$ and every $k\in\operatorname{Her}(h)$,
--
--   $$
--   \Phi\big(E_{ii_0}(k)\big)=E_{i_0i_0}\Big(\Phi\big(E_{ii_0}(k)\big)_{i_0i_0}\Big),
--   $$
--
--   that is, every entry of the matrix $\Phi(E_{ii_0}(k))$ vanishes except possibly the $(i_0,i_0)$ entry.
--
--   Consequently, on the $i_0$-th column the transport is described by the $n$ maps $k\mapsto\Phi(E_{ii_0}(k))_{i_0i_0}$ with values in $A$. These are the maps that turn a matrix-level Cuntz comparison of $\operatorname{diag}_n(h)$ with a single corner into $n$ mutually orthogonal copies of $\operatorname{Her}(h)$ inside $A$.
--
--   **Formalization Note** The transport is a term `T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v)`, with fields `carrier` ($\Phi$, a continuous linear map), `hom` ($\theta$, a non-unital $*$-homomorphism), `inner`, `outer`, `mul`, `image`. The matrix $E_{ii_0}(k)$, viewed as an element of the hereditary subalgebra, is `entryHer i i₀ k`. Indices run over `Fin n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/OrthogonalSlots.lean#L211-L238

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots

open OAI OAI.MainGap OAI.MainGap.RegularTransport
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass
variable {A : Type*} [NonUnitalCStarAlgebra A]
open scoped CStarAlgebra
variable {n : ℕ} {h v : A} (i₀ : Fin n)
    (T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v))

theorem OAI.MainGap.RegularTransport.carrier_entryHer (i : Fin n) (k : Her h) :
    T.carrier (entryHer i i₀ k) =
      entry i₀ i₀ ((T.carrier (entryHer i i₀ k)) i₀ i₀) := by sorry
