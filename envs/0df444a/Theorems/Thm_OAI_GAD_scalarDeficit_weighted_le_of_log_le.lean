-- Prove2me | Theorems.Thm_OAI_GAD_scalarDeficit_weighted_le_of_log_le
-- name    : OAI.GAD.scalarDeficit_weighted_le_of_log_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:20:51.094536+00:00
-- url     : https://prove2.me/theorems/2eea1ef3-bcb6-4b43-a01b-79c13de015a2
-- title:
--   Weighted scalar entropy deficits inherit logarithmic comparisons
-- statement:
--   For $x,y,z\ge0$ let $\lambda_\pm=\frac12\bigl((x+y+z)\pm\sqrt{(x+y+z)^2-4yz}\bigr)$, write $\eta(w)=-w\log w$ (natural logarithm, $\eta(0)=0$), and define the scalar entropy deficit and its logarithmic counterpart
--   $$\Delta(x,y,z)=\eta(x)+\eta(y)+\eta(z)-\eta(\lambda_+)-\eta(\lambda_-),\qquad \delta(x,y,z;t)=\log\Bigl(1+\frac xt\Bigr)-\log\Bigl(1+\frac{tx}{(t+y)(t+z)}\Bigr)\quad(t>0).$$
--   Let $\alpha$ be a finite index set, and for $i\in\alpha$ let $c_i$ be real numbers (of arbitrary sign) and $x_i,y_i,z_i\ge0$. If $\sum_{i\in\alpha}c_i\,\delta(x_i,y_i,z_i;t)\le0$ for every $t>0$, then
--
--   $$
--   \sum_{i\in\alpha}c_i\,\Delta(x_i,y_i,z_i)\le0.
--   $$
--
--   Any finite linear inequality between scalar deficits is thereby reduced to the same inequality between the explicit functions $\delta(\cdot\,;t)$, uniformly in $t>0$. This is the workhorse behind the vanishing, monotonicity, concavity and superadditivity properties of $\Delta$.
--
--   **Formalization Note** $\Delta$ is `scalarDeficit`, $\delta$ is `deficitLog`, and $\lambda_\pm$ are `blockLambdaPlus` and `blockLambdaMinus`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean#L91-L106

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
universe u_1 u_2
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
open Matrix Set

theorem OAI.GAD.scalarDeficit_weighted_le_of_log_le {α : Type u_1} [Fintype α]
    (c x y z : α → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) (hz : ∀ i, 0 ≤ z i)
    (hlog : ∀ t : ℝ, 0 < t → ∑ i, c i * deficitLog (x i) (y i) (z i) t ≤ 0) :
    ∑ i, c i * scalarDeficit (x i) (y i) (z i) ≤ 0 := by sorry
