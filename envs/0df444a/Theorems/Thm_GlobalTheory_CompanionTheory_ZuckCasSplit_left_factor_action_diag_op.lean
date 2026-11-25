-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_left_factor_action_diag_op
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.left_factor_action_diag_op
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:30:32.395571+00:00
-- url     : https://prove2.me/theorems/41bb50a2-38e3-49c4-8ed1-2651e42de0de
-- title:
--   Zuck Cas Split: left factor action diag op
-- statement:
--   The Zuck Cas Split construction uses the left factor action diag op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L147-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L147-L147

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

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.left_factor_action_diag_op (T : Module.End ℂ V) : (on1 (dOp ι T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := by sorry
