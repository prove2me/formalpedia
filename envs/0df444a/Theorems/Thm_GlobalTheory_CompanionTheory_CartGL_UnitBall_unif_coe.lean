-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_unif_coe
-- name    : GlobalTheory.CompanionTheory.CartGL.UnitBall.unif_coe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:51.500066+00:00
-- url     : https://prove2.me/theorems/5fd49ad1-f389-4949-b42c-4d48d36b1bf5
-- title:
--   Unit Ball: unif coe
-- statement:
--   The Unit Ball construction uses the unif coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecompositionGlNonarchimedean.lean#L61-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CartanDecompositionGlNonarchimedean.lean#L61-L61

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedean
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.UnitBall
variable (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
variable {L}
variable {p : Lˣ}

theorem GlobalTheory.CompanionTheory.CartGL.UnitBall.unif_coe (hp : IsUnif p) : ((unif hp : ball L) : L) = p := by sorry
