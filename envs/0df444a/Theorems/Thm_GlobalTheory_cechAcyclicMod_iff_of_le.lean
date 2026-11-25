-- Prove2me | Theorems.Thm_GlobalTheory_cechAcyclicMod_iff_of_le
-- name    : GlobalTheory.cechAcyclicMod_iff_of_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:45.792191+00:00
-- url     : https://prove2.me/theorems/e32f1c7a-e06d-5a89-bef7-483356f41e4b
-- title:
--   Global Theory: cech Acyclic Mod iff of le
-- statement:
--   The Global Theory construction uses the cech Acyclic Mod iff of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L300-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CechModulesFunctorShortExactOfAcyclic.lean#L300-L306

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}} {ι : Type}
variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}

theorem GlobalTheory.cechAcyclicMod_iff_of_le (h : ∀ i, U i ≤ V) : CechAcyclicMod V U F ↔
    ∀ s : Finset ι, s.Nonempty → ∀ q, 0 < q → Subsingleton (cohOn F (⨅ i ∈ s, U i) q) := by sorry
