-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_exists_eq_smul_subgroup
-- name    : GlobalTheory.CompanionTheory.HaarPK.exists_eq_smul_subgroup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:53.003735+00:00
-- url     : https://prove2.me/theorems/35eaf813-7653-4488-bdb3-04b690c6da4d
-- title:
--   Haar PK: exists eq smul subgroup
-- statement:
--   The Haar PK construction uses the exists eq smul subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L200-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L200-L237

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

theorem GlobalTheory.CompanionTheory.HaarPK.exists_eq_smul_subgroup [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    (P : Subgroup G) (hP : IsClosed (P : Set G)) (μ ν : Measure G)
    (hμ1 : μ (P : Set G)ᶜ = 0) (hμ2 : ∀ p ∈ P, μ.map (fun x => p * x) = μ)
    (hμ3 : ∀ s : Set G, IsCompact s → μ s ≠ ⊤) (hμ4 : μ ≠ 0)
    (hν1 : ν (P : Set G)ᶜ = 0) (hν2 : ∀ p ∈ P, ν.map (fun x => p * x) = ν)
    (hν3 : ∀ s : Set G, IsCompact s → ν s ≠ ⊤) (hν4 : ν ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by sorry
