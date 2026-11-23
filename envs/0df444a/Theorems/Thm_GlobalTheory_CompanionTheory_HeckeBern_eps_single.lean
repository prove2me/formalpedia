-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_eps_single
-- name    : GlobalTheory.CompanionTheory.HeckeBern.eps_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:38.733883+00:00
-- url     : https://prove2.me/theorems/409779c8-11ae-49a4-be96-b285463c7141
-- title:
--   Hecke Bern: eps single
-- statement:
--   The Hecke Bern construction uses the eps single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L23-L24

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

theorem GlobalTheory.CompanionTheory.HeckeBern.eps_single (x : G ⧸ K) (c : ℂ) : eps K (Finsupp.single x c) = c := by sorry
