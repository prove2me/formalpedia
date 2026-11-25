-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_dR_tens
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.dR_tens
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:25:22.969254+00:00
-- url     : https://prove2.me/theorems/c02af25d-a96f-5cff-a2ba-ec78fd031565
-- title:
--   Zuck Cas Split: d R tens
-- statement:
--   The Zuck Cas Split construction uses the d R tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L81-L86

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

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.dR_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) {X : Mx k r} (hX : InLieHpk k r X) :
    (F.tens F').dR X = F.dR X ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dR X := by sorry
