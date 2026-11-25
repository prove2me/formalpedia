-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_dC_tens
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.dC_tens
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:25:17.123217+00:00
-- url     : https://prove2.me/theorems/cfe5c92a-812c-5b99-9477-9dbaec4ea202
-- title:
--   Zuck Cas Split: d C tens
-- statement:
--   The Zuck Cas Split construction uses the d C tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L88-L92

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

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.dC_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) (Y : Mx k r) :
    (F.tens F').dC Y = F.dC Y ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dC Y := by sorry
