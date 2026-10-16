-- Prove2me | Theorems.Thm_OAI_CrossEnsemble_operator_comp_left
-- name    : OAI.CrossEnsemble.operator_comp_left
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:03:44.543713+00:00
-- url     : https://prove2.me/theorems/8540ecdd-daa0-42a7-9575-3f5dadbf1fef
-- title:
--   Composing a square-summable sum of rank-one operators on the left
-- statement:
--   Let $E$ be a complex Hilbert space, let $I$ be an index set, and let $u,v:I\to E$ be families with $\sum_i\|u_i\|^2<\infty$ and $\sum_i\|v_i\|^2<\infty$. Define the bounded operator
--   $$O(u,v)=\sum_{i\in I}|u_i\rangle\langle v_i|,\qquad\text{i.e.}\quad O(u,v)\,x=\sum_{i\in I}\langle v_i,x\rangle\,u_i,$$
--   where the series converges absolutely in operator norm. Then for every bounded operator $Z$ on $E$,
--   $$Z\circ O(u,v)=O\big((Zu_i)_{i\in I},\,v\big).$$
--
--   Operators of the form $O(u,v)$ are trace-class operators presented by two square-summable families of vectors. This rule moves an operator applied on the left into the vectors $u_i$. Together with the corresponding statement for adjoints, it is the ingredient for the sandwich formula $Z\,O(u,v)\,Z^{*}=O(Zu,Zv)$, which describes how such operators transform under conjugation, for example by a beam-splitter unitary.
--
--   **Formalization Note** $O(u,v)$ is `CrossEnsemble.operator u v`, defined as the `tsum` of `InnerProductSpace.rankOne ℂ (u i) (v i)`. Without the square-summability hypotheses that `tsum` could default to $0$; with them it is a genuine convergent sum.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Fock/Operators.lean#L487-L501

import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators

open OAI OAI.CrossEnsemble
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.CrossEnsemble.operator_comp_left {u v : I → E} (hu : Summable (fun i => ‖u i‖^2))
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Z ∘L operator u v=operator (fun i => Z (u i)) v := by sorry
