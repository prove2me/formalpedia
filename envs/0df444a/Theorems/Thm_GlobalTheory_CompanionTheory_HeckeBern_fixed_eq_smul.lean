-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBern_fixed_eq_smul
-- name    : GlobalTheory.CompanionTheory.HeckeBern.fixed_eq_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:45:04.15538+00:00
-- url     : https://prove2.me/theorems/64f778f0-1e4c-4957-89e6-e3157c1cc7ec
-- title:
--   Hecke Bern: fixed eq smul
-- statement:
--   The Hecke Bern construction uses the fixed eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L48-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean#L48-L66

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

theorem GlobalTheory.CompanionTheory.HeckeBern.fixed_eq_smul (w : (G ⧸ K) →₀ ℂ) (hw : ∀ k ∈ K, lam K k w = w) (u : G) (S : Finset (G ⧸ K))
    (hS : (↑S : Set (G ⧸ K)) = MulAction.orbit K (u : G ⧸ K))
    (hsupp : ∀ y, y ∉ S → w y = 0) :
    w = w (u : G ⧸ K) • ∑ y ∈ S, Finsupp.single y (1 : ℂ) := by sorry
