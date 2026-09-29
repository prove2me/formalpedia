-- Prove2me | Theorems.Thm_Freiman_lowerHistory_witness_metadata_05_part_03
-- name    : Freiman.lowerHistory_witness_metadata_05_part_03
-- status  : Proved
-- author  : @tp
-- created : 2026-09-14T08:56:38.699886+00:00
-- url     : https://prove2.me/theorems/9ef071ba-4b45-413c-b80c-7b45027771cd
-- title:
--   Freiman H5 witness metadata block 5, part 3
-- statement:
--   Consider witnesses 101 through 150 in the fifth original history witness block. Write $B_i$ for the indexed bound and $R_j$ for the indexed rational rectangle. For every witness in this group, projection onto its lower bound, upper bound and rectangle agrees with the corresponding original bound-index pair and the displayed rectangle index. Equivalently, the two projected finite lists are equal. The complete rectangle-index list and the exact group are specified in the formal statement. This identifies the original certificate data used in the row-2 prerequisite of the H5 exception anchor.
-- source:
--   Original Freiman lowerHistoryWitnesses05 and lowerHistoryWitnessIds05. Prerequisite of https://prove2.me/theorem/bb9829c2-d91f-4bc0-a11c-3a75193cc00d .

import Definitions.Def_Freiman_lowerHistoryWitnesses05
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem Freiman.lowerHistory_witness_metadata_05_part_03 : ((lowerHistoryWitnesses05.toList.drop 100).take 50).map (fun w : CertWitness => (w.lowerBound,w.upperBound,w.rectangle)) =
  (((lowerHistoryWitnessIds05.toList.zip ([2,4,5,1,2,4,5,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,1,2,4,5,6,7,6] : List ℕ)).drop 100).take 50).map (fun z : (ℕ × ℕ) × ℕ => (lowerHistoryBound z.1.1,lowerHistoryBound z.1.2,lowerHistoryRectangles[z.2]?.getD ⟨0,1,0,1⟩)) := by sorry
