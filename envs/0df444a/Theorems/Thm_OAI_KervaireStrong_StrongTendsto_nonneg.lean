-- Prove2me | Theorems.Thm_OAI_KervaireStrong_StrongTendsto_nonneg
-- name    : OAI.KervaireStrong.StrongTendsto.nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:33:22.101237+00:00
-- url     : https://prove2.me/theorems/582d9a7b-64ad-4aae-9142-dcd5a0c05f18
-- title:
--   Strong limits of positive operators are positive
-- statement:
--   Let $T_i$ be positive operators on a complex Hilbert space converging strongly to $S$ along a nontrivial filter. Then
--   $$
--   S\ge0 .
--   $$
--
--   The positive cone is closed in the strong operator topology.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/StrongLimits.lean#L89-L103

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
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
open scoped ComplexOrder

theorem OAI.KervaireStrong.StrongTendsto.nonneg {T : ι → Operator K} {S : Operator K} [l.NeBot]
    (h : StrongTendsto T l S) (hp : ∀ i, 0 ≤ T i) : 0 ≤ S := by sorry
