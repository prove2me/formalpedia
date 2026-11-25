-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckTensHom_sn_tens1
-- name    : GlobalTheory.CompanionTheory.ZuckTensHom.sn_tens1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:02:12.166578+00:00
-- url     : https://prove2.me/theorems/15ae6925-ac22-48b3-b6d2-7747bf1849f6
-- title:
--   Zuck Tens Hom: sn tens1
-- statement:
--   The Zuck Tens Hom construction uses the sn tens1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L47-L51

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

theorem GlobalTheory.CompanionTheory.ZuckTensHom.sn_tens1 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (F.tens E, U)) :
    sn (F.tens E, U) W x = ∑ e, sn (F, U) W (fun c => x (c, e)) := by sorry
