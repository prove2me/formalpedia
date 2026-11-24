-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_exists_integral_basis
-- name    : GlobalTheory.CompanionTheory.SW.FD.exists_integral_basis
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:33.83215+00:00
-- url     : https://prove2.me/theorems/b7a8c5a9-da2d-40f8-ac91-00c4378e340c
-- title:
--   FD: exists integral basis
-- statement:
--   The FD construction uses the exists integral basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L57-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L57-L82

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

theorem GlobalTheory.CompanionTheory.SW.FD.exists_integral_basis [DecidableEq (InfinitePlace F)] (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    ∃ B : Module.Basis (InfinitePlace F) ℤ (𝓞 F),
      (Matrix.det (Matrix.of fun i w => ρ w ((B i : 𝓞 F) : F))) ^ 2 = (discr F : ℝ) := by sorry
