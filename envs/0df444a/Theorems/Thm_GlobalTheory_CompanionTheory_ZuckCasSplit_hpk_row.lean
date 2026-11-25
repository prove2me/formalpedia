-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_hpk_row
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_row
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:12.693895+00:00
-- url     : https://prove2.me/theorems/98abd69d-478f-472f-af1a-a5f0cb3d4cda
-- title:
--   Zuck Cas Split: hpk row
-- statement:
--   The Zuck Cas Split construction uses the hpk row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L22-L34

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCasSplit
open Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk)
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_row (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    ∃ (j₀ : Fin (2 * r + k + 1)) (s : ℂ), s * s = 1 ∧ (∀ j, Formalism.QuantumDeterminants.Hpk k r i j = if j = j₀ then s else 0) ∧
      ∀ j, Formalism.QuantumDeterminants.Hpk k r j₀ j = if j = i then s else 0 := by sorry
