-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckTensHom_act_tens2
-- name    : GlobalTheory.CompanionTheory.ZuckTensHom.act_tens2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:14.033119+00:00
-- url     : https://prove2.me/theorems/14880420-8f96-47f7-a6aa-9f12b8bff4fb
-- title:
--   Zuck Tens Hom: act tens2
-- statement:
--   The Zuck Tens Hom construction uses the act tens2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SnTens2.lean#L36-L45

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

theorem GlobalTheory.CompanionTheory.ZuckTensHom.act_tens2 (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (E.tens F, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (e', c')) := by sorry
