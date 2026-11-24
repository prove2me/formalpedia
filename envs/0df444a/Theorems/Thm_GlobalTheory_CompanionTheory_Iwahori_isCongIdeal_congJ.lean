-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_isCongIdeal_congJ
-- name    : GlobalTheory.CompanionTheory.Iwahori.isCongIdeal_congJ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:16.269596+00:00
-- url     : https://prove2.me/theorems/8e030ec9-dd6c-4688-a6da-1bf3ec9052f3
-- title:
--   Iwahori: is Cong Ideal cong J
-- statement:
--   The Iwahori construction uses the is Cong Ideal cong J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriStatement.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IwahoriStatement.lean#L18-L32

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorizationStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLowerStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugationPreservesCongruenceStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HermitianAdjointExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceEndomorphismInverseExistsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpperStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori

theorem GlobalTheory.CompanionTheory.Iwahori.isCongIdeal_congJ {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] {Λ : AddSubgroup V} (hΛ : IsLat L Λ)
    {π : L} (hπ : ‖π‖ < 1) {ι : Type} (P : ι → Module.End L V)
    (hP : ∀ i, ∀ x ∈ Λ, P i x ∈ Λ) : IsCongIdeal (congJ Λ π) P := by sorry
