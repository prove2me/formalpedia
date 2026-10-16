-- Prove2me | Theorems.Thm_OAI_GAD_exists_projected_factor
-- name    : OAI.GAD.exists_projected_factor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:32:34.166236+00:00
-- url     : https://prove2.me/theorems/716ad86e-1015-4e69-b75b-81362ab4de56
-- title:
--   Projecting a unit-norm factor into a subspace costs at most twice the lost mass
-- statement:
--   Let $\iota,\kappa$ be finite index sets. For $Z\in\mathbb{C}^{\iota\times\kappa}$ write $\|Z\|_F^2=\operatorname{Tr}(ZZ^{*})=\sum_{i,k}|Z_{ik}|^2$ for the squared Frobenius norm, where $Z^{*}$ is the conjugate transpose. Let $P\in\mathbb{C}^{\iota\times\iota}$ be an orthogonal projection, i.e. $P^{*}=P$ and $P^2=P$, and let $X,B\in\mathbb{C}^{\iota\times\kappa}$ satisfy $\|X\|_F=\|B\|_F=1$ and $PB=B$. Then there exists $Y\in\mathbb{C}^{\iota\times\kappa}$ with $\|Y\|_F=1$ and $PY=Y$ such that
--   $$
--   \|X-Y\|_F^2\le2\big(1-\|PX\|_F^2\big).
--   $$
--
--   Since $\|PX\|_F^2=\operatorname{Tr}(P\,XX^{*})$ is the probability that the measurement outcome $P$ occurs on the state $XX^{*}$, the lemma says that a unit-norm factor of a state can be replaced by a unit-norm factor lying entirely in the range of $P$, at squared distance at most twice the failure probability. The matrix $B$ only certifies that the range of $P$ contains some unit-norm factor; it is needed when $PX=0$. This is the basic step in approximately orthogonalizing well-decoded states.
--
--   **Formalization Note** The orthogonal projection hypothesis is `IsProjection P` (Hermitian and idempotent), and $\|Z\|_F^2$ is `mass Z`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/EntropyContinuity.lean#L290-L327

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

theorem OAI.GAD.exists_projected_factor {P : Matrix ι ι ℂ} (hP : IsProjection P)
    (X B : Matrix ι κ ℂ) (hX : mass X=1) (hB : mass B=1) (hPB : P*B=B) :
    ∃ Y : Matrix ι κ ℂ, mass Y=1 ∧ P*Y=Y ∧ mass (X-Y) ≤ 2*(1-mass (P*X)) := by sorry
