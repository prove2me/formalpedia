-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_exists_exhaustion
-- name    : GlobalTheory.CompanionTheory.SW.FibreFam.exists_exhaustion
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:20.982647+00:00
-- url     : https://prove2.me/theorems/db272db0-2d02-4e4e-8f98-610a9da0626e
-- title:
--   Fibre Fam: exists exhaustion
-- statement:
--   The Fibre Fam construction uses the exists exhaustion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L21-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L21-L44

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

theorem GlobalTheory.CompanionTheory.SW.FibreFam.exists_exhaustion [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} (hU : IsOpen U) :
    ∃ K W : ℕ → Set V, (∀ n, IsCompact (K n)) ∧ (∀ n, IsOpen (W n)) ∧ (∀ n, W n ⊆ K n) ∧
      (∀ n, K n ⊆ U) ∧ Monotone K ∧ Monotone W ∧ (⋃ n, K n) = U ∧ (⋃ n, W n) = U := by sorry
