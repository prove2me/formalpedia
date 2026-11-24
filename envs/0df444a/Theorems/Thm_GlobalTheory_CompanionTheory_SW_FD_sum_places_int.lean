-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_sum_places_int
-- name    : GlobalTheory.CompanionTheory.SW.FD.sum_places_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:31.193345+00:00
-- url     : https://prove2.me/theorems/2ac0074a-43a6-4468-adef-c6d824af90df
-- title:
--   FD: sum places int
-- statement:
--   The FD construction uses the sum places int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L92-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L92-L105

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FD
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.FD.sum_places_int (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : 𝓞 F) :
    ∃ z : ℤ, ∑ w, ρ w (a : F) = (z : ℝ) := by sorry
