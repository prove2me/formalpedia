-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_norm_det_sub_det_le
-- name    : GlobalTheory.CompanionTheory.CartGL.norm_det_sub_det_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:51.873116+00:00
-- url     : https://prove2.me/theorems/c3df7987-12de-4be2-87b6-cacb492ac18b
-- title:
--   Cart GL: norm det sub det le
-- statement:
--   The Cart GL construction uses the norm det sub det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MatrixNearIdentityInCongruenceSubgroup.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/MatrixNearIdentityInCongruenceSubgroup.lean#L20-L33

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

theorem GlobalTheory.CompanionTheory.CartGL.norm_det_sub_det_le {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (hAB : ∀ i j, ‖(A - B) i j‖ ≤ r) :
    ‖A.det - B.det‖ ≤ r := by sorry
