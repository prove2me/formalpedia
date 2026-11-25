-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ZuckUIso_res_coe
-- name    : GlobalTheory.CompanionTheory.ZuckUIso.res_coe
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:02:34.560149+00:00
-- url     : https://prove2.me/theorems/77443ba3-e278-45ba-a7d7-ca95fbae881a
-- title:
--   Zuck UIso: res coe
-- statement:
--   The Zuck UIso construction uses the res coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UnitaryIso.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/UnitaryIso.lean#L50-L52

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

theorem GlobalTheory.CompanionTheory.ZuckUIso.res_coe (U U' : URep k r) (e : U.R.H →L[ℂ] U'.R.H)
    (he : ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) (v : U.R.smSub) :
    (res U U' e he v : U'.R.H) = e v := by sorry
