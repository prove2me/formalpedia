-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_right_factor_action_kronecker
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.right_factor_action_kronecker
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:38.784125+00:00
-- url     : https://prove2.me/theorems/33023b7a-cdb9-48c8-a93f-d72d931fd7b9
-- title:
--   Zuck Cas Split: right factor action kronecker
-- statement:
--   The Zuck Cas Split construction uses the right factor action kronecker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L156-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L156-L159

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
set_option linter.unusedSectionVars false
variable {ι κ V : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.right_factor_action_kronecker (A : Matrix κ κ ℂ) :
    (on2 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct ((1 : Matrix ι ι ℂ) ⊗ₖ A) := by sorry
