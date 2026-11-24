-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_IwahoriLU_blk_lc
-- name    : GlobalTheory.CompanionTheory.CartGL.IwahoriLU.blk_lc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:33.258241+00:00
-- url     : https://prove2.me/theorems/786fdb66-c8e8-4ded-a50e-34046812295e
-- title:
--   Iwahori LU: blk lc
-- statement:
--   The Iwahori LU construction uses the blk lc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NearIdentityUpperLowerFactorization.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NearIdentityUpperLowerFactorization.lean#L28-L29

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FactorizationBis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.IwahoriLU
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
omit [IsUltrametricDist L]

theorem GlobalTheory.CompanionTheory.CartGL.IwahoriLU.blk_lc (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) (j : Fin n) :
    blk P b c d (Fin.last n) j.castSucc = c j := by sorry
