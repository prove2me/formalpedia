-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_smul_mk
-- name    : GlobalTheory.CompanionTheory.HeckeBern.smul_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:47.610518+00:00
-- url     : https://prove2.me/theorems/c41419d1-e391-4335-8d36-b5ee24fcc7d6
-- title:
--   Hecke Bern: smul mk
-- statement:
--   The Hecke Bern construction uses the smul mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L17-L17

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

theorem GlobalTheory.CompanionTheory.HeckeBern.smul_mk (g x : G) : g • (x : G ⧸ K) = ((g * x : G) : G ⧸ K) := by sorry
