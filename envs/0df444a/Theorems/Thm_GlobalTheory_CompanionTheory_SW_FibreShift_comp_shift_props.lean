-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreShift_comp_shift_props
-- name    : GlobalTheory.CompanionTheory.SW.FibreShift.comp_shift_props
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:04:43.490716+00:00
-- url     : https://prove2.me/theorems/64449863-ac09-4023-b148-715733bfde4f
-- title:
--   Fibre Shift: comp shift props
-- statement:
--   The Fibre Shift construction uses the comp shift props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationHaarBase.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DisintegrationHaarBase.lean#L11-L33

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationHaarBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreShift

theorem GlobalTheory.CompanionTheory.SW.FibreShift.comp_shift_props {V : Type} [TopologicalSpace V] [T2Space V] {W : Set V} (hW : IsOpen W)
    {T T' : V → V} (hT : ContinuousOn T W) (hT' : ContinuousOn T' W)
    (hmem : ∀ v, T v ∈ W ↔ v ∈ W) (hmem' : ∀ v, T' v ∈ W ↔ v ∈ W)
    (hinv : ∀ v ∈ W, T' (T v) = v) {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ W) :
    Continuous (fun v => φ (T v)) ∧ HasCompactSupport (fun v => φ (T v)) ∧
      tsupport (fun v => φ (T v)) ⊆ W := by sorry
