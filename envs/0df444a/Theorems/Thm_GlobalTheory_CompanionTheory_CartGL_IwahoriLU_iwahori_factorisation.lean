-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_IwahoriLU_iwahori_factorisation
-- name    : GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:52.650243+00:00
-- url     : https://prove2.me/theorems/a287aebe-21cf-49d6-ae3d-dfc6e18e64d9
-- title:
--   Iwahori LU: iwahori factorisation
-- statement:
--   The Iwahori LU construction uses the iwahori factorisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NearIdentityUpperLowerFactorization.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/NearIdentityUpperLowerFactorization.lean#L41-L45

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

theorem GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r < 1) (A : Matrix (Fin n) (Fin n) L) (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) :
    ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
      (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W := by sorry
