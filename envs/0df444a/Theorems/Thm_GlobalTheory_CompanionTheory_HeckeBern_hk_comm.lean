-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_hk_comm
-- name    : GlobalTheory.CompanionTheory.HeckeBern.hk_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:43.29031+00:00
-- url     : https://prove2.me/theorems/005ed4bd-5cd6-449e-9082-f049bd1ee145
-- title:
--   Hecke Bern: hk comm
-- statement:
--   The Hecke Bern construction uses the hk comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L32-L35

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

theorem GlobalTheory.CompanionTheory.HeckeBern.hk_comm (A : Hk K) (g : G) (v : (G ⧸ K) →₀ ℂ) : A.1 (lam K g v) = lam K g (A.1 v) := by sorry
