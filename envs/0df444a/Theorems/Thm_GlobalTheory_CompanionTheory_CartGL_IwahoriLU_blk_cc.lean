-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_IwahoriLU_blk_cc
-- name    : GlobalTheory.CompanionTheory.CartGL.IwahoriLU.blk_cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:24.878984+00:00
-- url     : https://prove2.me/theorems/49697efb-9fd5-4f25-a6f1-57d51fca0e9e
-- title:
--   Iwahori LU: blk cc
-- statement:
--   The Iwahori LU construction uses the blk cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NearIdentityUpperLowerFactorization.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NearIdentityUpperLowerFactorization.lean#L20-L21

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

theorem GlobalTheory.CompanionTheory.CartGL.IwahoriLU.blk_cc (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) (i j : Fin n) :
    blk P b c d i.castSucc j.castSucc = P i j := by sorry
