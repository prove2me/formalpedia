-- Prove2me | Theorems.Thm_OAI_KervaireStrong_StrongTendsto_exp
-- name    : OAI.KervaireStrong.StrongTendsto.exp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:32:45.328472+00:00
-- url     : https://prove2.me/theorems/583049f2-b9cc-4c22-b1c3-ceae294b377d
-- title:
--   Strong limits commute with the exponential
-- statement:
--   Let $T_i$ be bounded operators on a Banach space with $\|T_i\|\le C$, converging strongly to $S$: $T_i\xi\to S\xi$ for every $\xi$. Then
--   $$
--   e^{T_i}\xi\to e^{S}\xi\qquad\text{for every }\xi .
--   $$
--
--   Uniform boundedness is essential, since multiplication is not jointly continuous in the strong topology.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/StrongLimits.lean#L47-L75

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits

open OAI OAI.KervaireStrong
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}

theorem OAI.KervaireStrong.StrongTendsto.exp [CompleteSpace H] {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C) :
    StrongTendsto (fun i => NormedSpace.exp (T i)) l (NormedSpace.exp S) := by sorry
