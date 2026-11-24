-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_exists_real_basis
-- name    : GlobalTheory.CompanionTheory.SW.FD.exists_real_basis
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:03:40.202848+00:00
-- url     : https://prove2.me/theorems/e85db07d-0682-4c4f-9a37-24d17f7f5a5b
-- title:
--   FD: exists real basis
-- statement:
--   The FD construction uses the exists real basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L84-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L84-L90

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

theorem GlobalTheory.CompanionTheory.SW.FD.exists_real_basis {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ) (h : A.det ≠ 0) :
    ∃ b : Module.Basis ι ℝ (ι → ℝ), ∀ i, b i = A i := by sorry
