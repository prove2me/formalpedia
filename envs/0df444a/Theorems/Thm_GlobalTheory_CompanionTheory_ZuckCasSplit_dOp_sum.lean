-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_dOp_sum
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.dOp_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:26:54.255387+00:00
-- url     : https://prove2.me/theorems/eece5a77-d3f7-431a-93e9-39f3b384e3af
-- title:
--   Zuck Cas Split: d Op sum
-- statement:
--   The Zuck Cas Split construction uses the d Op sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L120-L123

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

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.dOp_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ V) :
    (dOp ι (∑ a ∈ s, T a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, dOp ι (T a) := by sorry
