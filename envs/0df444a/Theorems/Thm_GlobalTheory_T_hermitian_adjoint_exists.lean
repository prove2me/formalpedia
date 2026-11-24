-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_adjoint_exists
-- name    : GlobalTheory.T.hermitian_adjoint_exists
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:45:02.880096+00:00
-- url     : https://prove2.me/theorems/aa82541d-184d-4d8c-845f-b1c6b0fa80ec
-- title:
--   T: hermitian adjoint exists
-- statement:
--   The T construction uses the hermitian adjoint exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HermitianAdjointExistsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HermitianAdjointExistsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HermitianAdjointExists
import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HermitianAdjointExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitian_adjoint_exists : ∀ {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V] [FiniteDimensional L V] (s : L →+* L), IsInv s → ∀ h : V → V → L, IsHerm s h → ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y) := by sorry
