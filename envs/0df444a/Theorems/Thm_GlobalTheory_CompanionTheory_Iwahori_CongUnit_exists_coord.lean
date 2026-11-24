-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_CongUnit_exists_coord
-- name    : GlobalTheory.CompanionTheory.Iwahori.CongUnit.exists_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:15.117915+00:00
-- url     : https://prove2.me/theorems/844df2ce-b3da-4e1c-8522-5700bfe53afa
-- title:
--   Cong Unit: exists coord
-- statement:
--   The Cong Unit construction uses the exists coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceEndomorphismInverseExists.lean#L17-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceEndomorphismInverseExists.lean#L17-L62

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

theorem GlobalTheory.CompanionTheory.Iwahori.CongUnit.exists_coord {m : ℕ} (b : Module.Basis (Fin m) L V) {Λ : AddSubgroup V}
    (hb : ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1) {π : L} (hπ : ‖π‖ < 1)
    {g : Module.End L V} (hg : g ∈ congJ Λ π) {x : V} (hx : x ≠ 0) :
    ∃ i, (∀ j, ‖b.repr x j‖ ≤ ‖b.repr x i‖) ∧ b.repr x i ≠ 0 ∧
      ‖b.repr ((1 + g) x) i‖ = ‖b.repr x i‖ := by sorry
