-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_exists_bump
-- name    : GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:04.988092+00:00
-- url     : https://prove2.me/theorems/c8883cb0-96aa-46bc-b016-c6eb13dfed1e
-- title:
--   Fibre Fam: exists bump
-- statement:
--   The Fibre Fam construction uses the exists bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L14-L19

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreFam
variable {V : Type} [TopologicalSpace V]

theorem GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump [LocallyCompactSpace V] [T2Space V] {K O : Set V} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧ (∀ v, 0 ≤ φ v) ∧
      (∀ v, φ v ≤ 1) ∧ ∀ v ∈ K, φ v = 1 := by sorry
