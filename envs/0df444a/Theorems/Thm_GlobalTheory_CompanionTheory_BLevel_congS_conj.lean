-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_congS_conj
-- name    : GlobalTheory.CompanionTheory.BLevel.congS_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:20:52.5518+00:00
-- url     : https://prove2.me/theorems/2844a15a-84f9-40ce-9332-9edacc88e7d4
-- title:
--   BLevel: cong S conj
-- statement:
--   The BLevel construction uses the cong S conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L103-L112

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}

theorem GlobalTheory.CompanionTheory.BLevel.congS_conj {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) {c : GL (Fin m) L} (hc : c ∈ intS) (k : GL (Fin m) L) :
    k ∈ congS r h0 h1 ↔ c * k * c⁻¹ ∈ congS r h0 h1 := by sorry
