-- Prove2me | Theorems.Thm_OAI_PlanarL1_Columns_Model_World_run_success_probability
-- name    : OAI.PlanarL1.Columns.Model.World.run_success_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T11:59:41.328592+00:00
-- url     : https://prove2.me/theorems/f1ea5c03-14ad-441b-9096-14b5017aa273
-- title:
--   OAI.PlanarL1.Columns.Model.World.run_success_probability: intermediate lemma from OpenAI, Planar Graph Metrics Embed into L1 with Constant Distortion
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarL1.planar_graph_metrics_embed_L1`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Planar Graph Metrics Embed into L1 with Constant Distortion*, OpenAI Math Release, September 23, 2026, result family 89, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarL1.Columns.Model.World.run_success_probability` of [lean/OAI/Combinatorics/PlanarL1/PlanarL1/Schedule.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Schedule.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarL1.Columns.Model.World`, with `open Parameters`):
--
--   ```lean
--   lemma run_success_probability {f : ℕ} {x y : V} (hstart : W.Coherent x (targetRadius Q f 0))
--       (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
--       (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) :
--       successChance/2 ≤ (W.run g hm (f+1)).prob (fun Z => Z.Successful (Q*successGain) x y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarL1.Execution.prob`, `OAI.PlanarL1.Parameters.GoodSpacing`, `OAI.PlanarL1.Parameters.persistenceCount`, `OAI.PlanarL1.Parameters.successChance`, `OAI.PlanarL1.Parameters.successGain`, `OAI.PlanarL1.Parameters.targetRadius`, `OAI.PlanarL1.Columns.Model.World`, `OAI.PlanarL1.Columns.Model.World.Coherent`, `OAI.PlanarL1.Columns.Model.World.Successful`, `OAI.PlanarL1.Columns.Model.World.distance` and `OAI.PlanarL1.Columns.Model.World.run` (definitions bundle `OAIQ5T5000` of this split).
--
--   **Used by.** The proof of `OAI.PlanarL1.planar_graph_metrics_embed_L1` of this split imports it.
-- source:
--   OpenAI, Planar Graph Metrics Embed into L1 with Constant Distortion, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 89; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Planar-Graph-Metrics-Embed-into-L1-with-Constant-Distortion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PlanarL1/PlanarL1/Schedule.lean (declaration OAI.PlanarL1.Columns.Model.World.run_success_probability)

import Mathlib
import Definitions.Def_OAIQ5T5000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PlanarL1.Columns.Model.World
open Parameters
variable {k : ℕ} {V : Type*} [Fintype V] {Q : ℝ}
variable (g : GoodSpacing Q) (W : World k V Q) {m : ℕ} (hm : 0 < m)
lemma run_success_probability {f : ℕ} {x y : V} (hstart : W.Coherent x (targetRadius Q f 0))
    (hmesh : (f:ℝ)*persistenceCount/m ≤ 1/4) (hmany : 10000 ≤ m)
    (hlo : 1 ≤ Q^f*W.distance x y) (hhi : Q^f*W.distance x y < 2) :
    successChance/2 ≤ (W.run g hm (f+1)).prob (fun Z => Z.Successful (Q*successGain) x y) := by
  sorry
end PlanarL1.Columns.Model.World

end

end OAI
end
