-- Prove2me | Theorems.Thm_OAI_GAD_exists_unitary_singular_decomposition
-- name    : OAI.GAD.exists_unitary_singular_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:22:51.582749+00:00
-- url     : https://prove2.me/theorems/ec16a802-f6df-4dc3-9387-705c396a28a5
-- title:
--   Singular value decomposition of a square complex matrix
-- statement:
--   Let $\iota$ be a finite index set and let $A\in\mathbb{C}^{\iota\times\iota}$ be an arbitrary square complex matrix, possibly singular. Then there exist unitary matrices $U,V\in\mathbb{C}^{\iota\times\iota}$ and real numbers $s_i\ge0$ ($i\in\iota$) such that
--
--   $$
--   A=U\,\operatorname{diag}(s)\,V^*.
--   $$
--
--   This is the singular value decomposition, with both unitaries indexed by the same finite set as $A$ and no ordering imposed on the singular values $s_i$. It brings a square block to nonnegative diagonal form by independent unitary changes of basis on the left and on the right, which is how entropy bounds for Gram matrices of block matrices are reduced to the case of a diagonal block.
--
--   **Formalization Note** $U$ and $V$ are elements of `Matrix.unitaryGroup ι ℂ`, $V^*$ is `star V`, and $\operatorname{diag}(s)$ is `Matrix.diagonal` of the complexified vector $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/ZeroBlockEntropy.lean#L236-L293

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open scoped BigOperators ComplexOrder
open Matrix
variable {ι : Type u_19} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.exists_unitary_singular_decomposition (A : Matrix ι ι ℂ) :
    ∃ (U V : Matrix.unitaryGroup ι ℂ) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) ∧ A = (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i ↦ (s i : ℂ)) * star V := by sorry
