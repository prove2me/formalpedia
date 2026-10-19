-- Prove2me | Theorems.Thm_OAI_MainGap_FiniteCuntzLE_block
-- name    : OAI.MainGap.FiniteCuntzLE.block
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:13:13.52239+00:00
-- url     : https://prove2.me/theorems/4fac2472-4851-4be0-8ea8-a776fde06582
-- title:
--   Cuntz comparison of matrices over a C*-algebra is compatible with block-diagonal sums
-- statement:
--   Let $A$ be a possibly non-unital C$^*$-algebra. For $k,l\in\mathbb{N}$ let $M_{k\times l}(A)$ be the space of $k\times l$ matrices over $A$ and $M_k(A)=M_{k\times k}(A)$, with their C$^*$-norms; for finite matrices, norm convergence is the same as entrywise convergence. For $x\in M_{k\times l}(A)$, $x^*\in M_{l\times k}(A)$ is the conjugate transpose. For $d\in M_n(A)$ and $v\in M_m(A)$ (no positivity is assumed), write $d\precsim v$ if there is a sequence $(r_j)_{j\in\mathbb{N}}$ in $M_{m\times n}(A)$ with
--   $$r_j^*\,v\,r_j\longrightarrow d\qquad(j\to\infty).$$
--   For $x\in M_{m\times n}(A)$ and $y\in M_{p\times q}(A)$, the block-diagonal sum $x\oplus y\in M_{(m+p)\times(n+q)}(A)$ has $x$ in the upper-left block, $y$ in the lower-right block, and zeros elsewhere.
--
--   **Theorem.** Let $m,n,p,q\in\mathbb{N}$, $d\in M_n(A)$, $v\in M_m(A)$, $d'\in M_q(A)$ and $v'\in M_p(A)$. If $d\precsim v$ and $d'\precsim v'$, then
--   $$d\oplus d'\ \precsim\ v\oplus v' .$$
--
--   This is the additivity of matrix Cuntz comparison under direct sums. Combined with proper infiniteness of $v$ ($\operatorname{diag}(v,v)\precsim v$), it shows for instance that, for elements $u,w,v\in A$ viewed as $1\times1$ matrices, $u\precsim v$ and $w\precsim v$ imply $u+w\precsim v$, which is how comparison passes to sums and to ideals.
--
--   **Formalization Note** Matrices are `CStarMatrix (Fin k) (Fin l) A`, $d\precsim v$ is `FiniteCuntzLE d v`, and $x\oplus y$ is `matrixBlock x y`, built from `Matrix.fromBlocks x 0 0 y` reindexed by `finSumFinEquiv`. The spectral-order instances in scope play no role in the statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Comparison.lean#L240-L255

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem OAI.MainGap.FiniteCuntzLE.block {m n p q : ℕ}
    {d : CStarMatrix (Fin n) (Fin n) A} {v : CStarMatrix (Fin m) (Fin m) A}
    {d' : CStarMatrix (Fin q) (Fin q) A} {v' : CStarMatrix (Fin p) (Fin p) A}
    (h : FiniteCuntzLE d v) (h' : FiniteCuntzLE d' v') :
    FiniteCuntzLE (matrixBlock d d') (matrixBlock v v') := by sorry
