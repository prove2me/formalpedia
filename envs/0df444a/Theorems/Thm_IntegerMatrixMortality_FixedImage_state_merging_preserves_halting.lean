-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_state_merging_preserves_halting
-- name    : IntegerMatrixMortality.FixedImage.state_merging_preserves_halting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:07.644164+00:00
-- url     : https://prove2.me/theorems/13208154-53a6-45c2-927d-085dfdbc0e47
-- title:
--   Lemma B.1 — State merging preserves halting
-- statement:
--   Let U₂ be Ivanov's concrete 278-state two-counter machine, and let π identify the four triples in Table 2. Let U be the representative-based quotient. For every original state q, its quotient instruction is π applied to the original destinations. For every u,v∈ℕ, including zero,
--
--   $$\operatorname{Halts}_U(1,u,v)\iff\operatorname{Halts}_{U_2}(1,u,v).$$
--
--   The counts of increments of counters zero and one and conditional decrements of counters zero and one in U are exactly (88,73,80,28). This establishes consistency and the source-machine counts needed for the matrix budget.
--
--   Differences from the source:
--   - encoding: the fixed source machine and reversed program → the full 278-row table, representative quotient, and named reversed program P; reason: the definitions are the source construction, without a universality or simulation premise
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Lemma B.1, PDF p. 16 / printed p. 14

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem state_merging_preserves_halting
    : (∀ q ∈ Finset.Icc 1 278, U (mergeState q) = mapInstruction mergeState (U2 q)) ∧
      (∀ u v : ℕ, machineHalts U (1,u,v) ↔ machineHalts U2 (1,u,v)) ∧
      instructionCounts U uStates = (88,73,80,28) := by sorry

end IntegerMatrixMortality.FixedImage
