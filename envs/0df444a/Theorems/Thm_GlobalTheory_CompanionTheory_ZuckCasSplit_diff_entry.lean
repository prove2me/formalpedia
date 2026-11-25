-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCasSplit_diff_entry
-- name    : GlobalTheory.CompanionTheory.ZuckCasSplit.diff_entry
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:15.077682+00:00
-- url     : https://prove2.me/theorems/ddef9cec-275d-59a7-9034-827b7a257baf
-- title:
--   Zuck Cas Split: diff entry
-- statement:
--   The Zuck Cas Split construction uses the diff entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CasimirSplitting.lean#L72-L79

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem GlobalTheory.CompanionTheory.ZuckCasSplit.diff_entry {F : FRep k r} (hF : F.OK) {X : Mx k r} (hX : InLieHpk k r X) (c d : F.ι) :
    HasDerivAt (fun t : ℝ => F.ρ (NormedSpace.exp ((t : ℂ) • X)) c d) (F.dR X c d) 0 := by sorry
