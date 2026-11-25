-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckUIso_uIso
-- name    : GlobalTheory.CompanionTheory.ZuckUIso.uIso
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:01:12.304519+00:00
-- url     : https://prove2.me/theorems/680ef593-ad3c-409c-b206-4055f3954fe0
-- title:
--   Zuck UIso: u Iso
-- statement:
--   The Zuck UIso construction uses the u Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UnitaryIso.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UnitaryIso.lean#L73-L82

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UnitaryIso
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckUIso
open CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk dsigW)
variable {k r : ℕ}

theorem GlobalTheory.CompanionTheory.ZuckUIso.uIso : UIso := by sorry
