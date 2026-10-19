-- Prove2me | Theorems.Thm_OAI_MainGap_Stable_block_conjugate
-- name    : OAI.MainGap.Stable.block_conjugate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:59:14.978536+00:00
-- url     : https://prove2.me/theorems/38dcf529-90fb-4750-8f60-9eaec93cadcb
-- title:
--   Corner blocks in the stabilization: $[x^*\iota_m(v)\,x]_{n,n}=[x]_{m,n}^*\,v\,[x]_{m,n}$
-- statement:
--   Let $A$ be a C*-algebra, possibly non-unital, and for $n\in\mathbb{N}$ let $M_n(A)$ be the C*-algebra of $n\times n$ matrices over $A$. For $n\le N$ the *corner embedding* $M_n(A)\to M_N(A)$ places an $n\times n$ matrix in the upper left corner and fills the remaining entries with $0$; these maps are injective, isometric $*$-homomorphisms, compatible with one another. Let $A_\infty$ be the resulting algebraic direct limit of the $M_n(A)$, normed by the norms of the $M_n(A)$, and let the *stabilization* $\mathcal S(A)$ be its completion, a C*-algebra. Write $\iota_m:M_m(A)\to\mathcal S(A)$ for the canonical embeddings.
--
--   Every $x\in\mathcal S(A)$ has matrix entries $x_{ij}\in A$ for $i,j\in\mathbb{N}=\{0,1,2,\dots\}$: for $x=\iota_N(y)$ one sets $x_{ij}=y_{ij}$ if $i,j<N$ and $x_{ij}=0$ otherwise, and the contractive linear maps $x\mapsto x_{ij}$ are extended from $A_\infty$ to $\mathcal S(A)$ by continuity. For $m,n\in\mathbb{N}$ let
--   $$[x]_{m,n}=(x_{ij})_{i<m,\ j<n}\in M_{m,n}(A)$$
--   be the upper left $m\times n$ block of $x$, and for a rectangular matrix $y$ let $y^*$ be its conjugate transpose, $(y^*)_{ij}=(y_{ji})^*$.
--
--   **Theorem.** For all $m,n\in\mathbb{N}$, every $v\in M_m(A)$ and every $x\in\mathcal S(A)$,
--   $$\bigl[\,x^*\,\iota_m(v)\,x\,\bigr]_{n,n}=\bigl([x]_{m,n}\bigr)^*\,v\,[x]_{m,n} .$$
--   Equivalently, for all $i,j<n$,
--   $$\bigl(x^*\,\iota_m(v)\,x\bigr)_{ij}=\sum_{p<m}\sum_{q<m}(x_{pi})^*\,v_{pq}\,x_{qj}.$$
--
--   This is the multiplication rule for the infinite matrices of the stabilization when the middle factor is supported in an $m\times m$ corner: only the first $m$ rows of $x$ contribute. Its main use is to pass from comparison statements in $\mathcal S(A)$ to finite matrices: if $r_j^*\,\iota_m(v)\,r_j\to\iota_n(d)$ in $\mathcal S(A)$, then, by continuity of the block map, the finite matrices $\rho_j=[r_j]_{m,n}\in M_{m,n}(A)$ satisfy $\rho_j^*\,v\,\rho_j\to d$.
--
--   **Formalization Note** $\mathcal S(A)$ is `Stabilization A := UniformSpace.Completion (Algebraic A)`, where `Algebraic A` is the `DirectLimit` of `Mat A n = CStarMatrix (Fin n) (Fin n) A` along the padding homomorphisms `padHom`, and $\iota_m$ is `corner m`. The entry $x_{ij}$ is `entry i j x`, the extension `UniformSpace.Completion.extension` of the bounded entry map on `Algebraic A`, and $[x]_{m,n}$ is `block m n x : CStarMatrix (Fin m) (Fin n) A`; the right-hand side uses `conjTranspose`. The local instance `algebraicTopology''` equips `Algebraic A` with the topology of its norm; the order instances declared alongside it play no role in the statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/MatrixEntries.lean#L142-L160

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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_MatrixEntries

open OAI OAI.MainGap OAI.MainGap.Stable
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.Stable.blockConjugateOrder
attribute [local instance] OAI.MainGap.Stable.blockConjugateStarOrder
attribute [local instance] OAI.MainGap.Stable.algebraicTopology''
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.Stable.block_conjugate (m n : ℕ) (v : Mat A m) (x : Stabilization A) :
    block n n (star x * corner m v * x) =
      (block m n x).conjTranspose * v * block m n x := by sorry
