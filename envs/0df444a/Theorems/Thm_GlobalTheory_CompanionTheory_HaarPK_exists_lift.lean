-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_exists_lift
-- name    : GlobalTheory.CompanionTheory.HaarPK.exists_lift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:12.574341+00:00
-- url     : https://prove2.me/theorems/086d5b40-c7b5-4344-aaaf-f0d2593a006d
-- title:
--   Haar PK: exists lift
-- statement:
--   The Haar PK construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L102-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean#L102-L198

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

theorem GlobalTheory.CompanionTheory.HaarPK.exists_lift [SecondCountableTopology G] [T2Space G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (P K : Subgroup G) (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) :
    ∃ l : Measure G, l (P : Set G)ᶜ = 0 ∧ (∀ p ∈ P, l.map (fun x => p * x) = l) ∧
      (∀ s : Set G, IsCompact s → l s ≠ ⊤) ∧
      ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ x, ∀ k ∈ K, φ (x * k) = φ x) → ∫⁻ x, φ x ∂l = ∫⁻ x, φ x ∂μ := by sorry
