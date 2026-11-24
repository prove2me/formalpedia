-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_norm_det_le_one
-- name    : GlobalTheory.CompanionTheory.CartGL.norm_det_le_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:28.565798+00:00
-- url     : https://prove2.me/theorems/82636f42-5aff-423d-b4d4-b6f7792227f7
-- title:
--   Cart GL: norm det le one
-- statement:
--   The Cart GL construction uses the norm det le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MatrixNearIdentityInCongruenceSubgroup.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MatrixNearIdentityInCongruenceSubgroup.lean#L35-L41

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaE
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixNearIdentityInCongruenceSubgroup
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem GlobalTheory.CompanionTheory.CartGL.norm_det_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by sorry
