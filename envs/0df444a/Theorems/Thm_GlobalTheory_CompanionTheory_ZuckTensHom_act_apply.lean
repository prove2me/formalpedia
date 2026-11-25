-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckTensHom_act_apply
-- name    : GlobalTheory.CompanionTheory.ZuckTensHom.act_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:58:37.531795+00:00
-- url     : https://prove2.me/theorems/a5a98c1b-9004-545c-ad9e-7d81e171ce54
-- title:
--   Zuck Tens Hom: act apply
-- statement:
--   The Zuck Tens Hom construction uses the act apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L19-L23

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

theorem GlobalTheory.CompanionTheory.ZuckTensHom.act_apply (X : Obj k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M X) (c : X.1.ι) :
    CompanionTheory.Zuck.act X g x c = ∑ d, X.1.ρ g c d • X.2.sig g (x d) := by sorry
