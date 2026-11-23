-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_exists_eq_smul
-- name    : GlobalTheory.CompanionTheory.HaarPK.exists_eq_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:56.611716+00:00
-- url     : https://prove2.me/theorems/ffdb1168-d3e9-4977-b109-2c3c25b36337
-- title:
--   Haar PK: exists eq smul
-- statement:
--   The Haar PK construction uses the exists eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L14-L27

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.CompanionTheory.HaarPK.exists_eq_smul [LocallyCompactSpace G] [SecondCountableTopology G] (μ ν : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν]
    (hμ : μ ≠ 0) (hν : ν ≠ 0) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by sorry
