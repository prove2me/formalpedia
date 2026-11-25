-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckTensHom_sn_tens2
-- name    : GlobalTheory.CompanionTheory.ZuckTensHom.sn_tens2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:01:01.221709+00:00
-- url     : https://prove2.me/theorems/d7f3ef66-ad7e-4cbd-8bd0-9b0c1f440d33
-- title:
--   Zuck Tens Hom: sn tens2
-- statement:
--   The Zuck Tens Hom construction uses the sn tens2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L53-L57

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SnTens2
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckTensHom
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckTensHom.sn_tens2 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (E.tens F, U)) :
    sn (E.tens F, U) W x = ∑ e, sn (F, U) W (fun c => x (e, c)) := by sorry
