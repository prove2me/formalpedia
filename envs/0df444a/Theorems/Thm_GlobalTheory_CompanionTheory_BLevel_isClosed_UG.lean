-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BLevel_isClosed_UG
-- name    : GlobalTheory.CompanionTheory.BLevel.isClosed_UG
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:21:22.246561+00:00
-- url     : https://prove2.me/theorems/634fe3d0-56ea-4719-bf2f-2c9b923537fe
-- title:
--   BLevel: is Closed UG
-- statement:
--   The BLevel construction uses the is Closed UG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L244-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/LatticeCongruenceSubgroupsOpenCompact.lean#L244-L250

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

theorem GlobalTheory.CompanionTheory.BLevel.isClosed_UG {L : Type} [NontriviallyNormedField L] (s : L →+* L) (hs : ∀ x, ‖s x‖ = ‖x‖) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) L) : IsClosed (UG s J : Set (GL (Fin n) L)) := by sorry
