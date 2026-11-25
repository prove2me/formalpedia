-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_left_factor_action_sum
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.left_factor_action_sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:28:15.384264+00:00
-- url     : https://prove2.me/theorems/745ad2f6-99ff-57f0-980f-f659cce1d0ee
-- title:
--   Zuck Cas Split: left factor action sum
-- statement:
--   The Zuck Cas Split construction uses the left factor action sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L137-L140

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

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.left_factor_action_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ (ι → V)) :
    (on1 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on1 (T a) := by sorry
