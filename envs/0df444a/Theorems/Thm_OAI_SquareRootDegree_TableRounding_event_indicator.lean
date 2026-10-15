-- Prove2me | Theorems.Thm_OAI_SquareRootDegree_TableRounding_event_indicator
-- name    : OAI.SquareRootDegree.TableRounding.event_indicator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:55:28.533332+00:00
-- url     : https://prove2.me/theorems/c38fcb9c-70fb-4156-9358-6095c231c49a
-- title:
--   A selector–leaf table event is a soft switching weight with $0/1$ entries
-- statement:
--   Let $\iota$ be a finite set of leaves and $\beta$ any set. A table consists of a selector $S:\beta\to\iota$ and leaf tests $L_i:\beta\to\{\mathsf{false},\mathsf{true}\}$ for $i\in\iota$. For a point $(u,z)\in\beta\times\beta^\iota$, consisting of a fresh coordinate $u$ and old coordinates $z=(z_i)_{i\in\iota}$, the table event $E_{S,L}$ holds when the leaf selected by $u$ fails its test at its old coordinate and every other leaf passes:
--   $$E_{S,L}=\Big\{(u,z):\ L_{S(u)}\big(z_{S(u)}\big)=\mathsf{false}\ \text{ and }\ L_i(z_i)=\mathsf{true}\ \text{for all } i\neq S(u)\Big\}.$$
--   Write $\operatorname{bit}(\mathsf{true})=1$ and $\operatorname{bit}(\mathsf{false})=0$. Then for every $(u,z)\in\beta\times\beta^\iota$,
--
--   $$
--   \mathbf 1_{E_{S,L}}(u,z)=\sum_{i\in\iota}\mathbf 1[S(u)=i]\prod_{j\neq i}\operatorname{bit}\big(L_j(z_j)\big)-\prod_{j\in\iota}\operatorname{bit}\big(L_j(z_j)\big).
--   $$
--
--   The right-hand side is the soft switching weight $\sum_is_i(u)\prod_{j\neq i}w_j(z_j)-\prod_jw_j(z_j)$ evaluated at the $0/1$ weights $s_i=\mathbf 1[S=i]$ and $w_j=\operatorname{bit}\circ L_j$. Hence identities proved for soft switching weights, such as the closed-form deficit, apply to deterministic table events; and since the soft weight is linear in the selector weights and multilinear in the leaf weights of different leaves, averaging this identity over independently randomised tables recovers soft weights with fractional values, which is how soft weights are rounded to deterministic tables.
--
--   **Formalization Note** The event is `tableEvent S L`, and the right-hand side is `softWeight (fun i b => if S b = i then 1 else 0) (fun i b => bit (L i b))`. No finiteness of $\beta$ is required.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Rounding.lean#L102-L130

import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding

open OAI OAI.SquareRootDegree OAI.SquareRootDegree.TableRounding
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
attribute [local instance] Classical.propDecidable
open FiniteRounding SoftEvent
attribute [local instance] Classical.propDecidable
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

omit [Fintype β] in
theorem OAI.SquareRootDegree.TableRounding.event_indicator (S : β → ι) (L : ι → β → Bool) (x : β × (ι → β)) :
    (if tableEvent S L x then (1:ℝ) else 0) =
      softWeight (fun i b => if S b = i then 1 else 0) (fun i b => bit (L i b)) x := by sorry
