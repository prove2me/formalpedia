-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_flip_facts
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.flip_facts
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:23:10.813522+00:00
-- url     : https://prove2.me/theorems/993354ec-625f-59ae-a2ba-414efaa4ded1
-- title:
--   Zuck Cas Split: flip facts
-- statement:
--   The Zuck Cas Split construction uses the flip facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L45-L50

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

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.flip_facts {n : ℕ} (Hm Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Hmᴴ = Hm) (h2 : Hm * Hm = 1) :
    (Hm * Yᴴ * Hm)ᴴ * Hm = Hm * Y ∧ Hm * (Hm * Yᴴ * Hm) = Yᴴ * Hm := by sorry
