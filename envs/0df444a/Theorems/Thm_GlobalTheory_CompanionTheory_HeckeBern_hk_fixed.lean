-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_hk_fixed
-- name    : GlobalTheory.CompanionTheory.HeckeBern.hk_fixed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:45:54.578541+00:00
-- url     : https://prove2.me/theorems/e3208276-ddc4-4704-b06f-25403fbd0142
-- title:
--   Hecke Bern: hk fixed
-- statement:
--   The Hecke Bern construction uses the hk fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L45-L46

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}

theorem GlobalTheory.CompanionTheory.HeckeBern.hk_fixed (A : Hk K) {k : G} (hk : k ∈ K) : lam K k (A.1 (dd K)) = A.1 (dd K) := by sorry
