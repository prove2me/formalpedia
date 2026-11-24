-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_CongUnit_mem_of_apply_mem
-- name    : GlobalTheory.CompanionTheory.Iwahori.CongUnit.mem_of_apply_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:50.913605+00:00
-- url     : https://prove2.me/theorems/28a7fcaf-dc88-4f41-87e0-42991a243622
-- title:
--   Cong Unit: mem of apply mem
-- statement:
--   The Cong Unit construction uses the mem of apply mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceEndomorphismInverseExists.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceEndomorphismInverseExists.lean#L72-L80

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceEndomorphismInverseExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.CongUnit
variable {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
  [Module L V]

theorem GlobalTheory.CompanionTheory.Iwahori.CongUnit.mem_of_apply_mem {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hG : (1 + g) x ∈ Λ) : x ∈ Λ := by sorry
