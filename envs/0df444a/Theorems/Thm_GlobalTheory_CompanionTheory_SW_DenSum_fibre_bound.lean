-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_DenSum_fibre_bound
-- name    : GlobalTheory.CompanionTheory.SW.DenSum.fibre_bound
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:03:53.322019+00:00
-- url     : https://prove2.me/theorems/ae832e7d-2c6f-4d20-b304-bf4d5bc24439
-- title:
--   Den Sum: fibre bound
-- statement:
--   The Den Sum construction uses the fibre bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DenominatorPowerSummable.lean#L35-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DenominatorPowerSummable.lean#L35-L133

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DenSum
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.DenSum.fibre_bound (N : ℕ) (hN : 0 < N) (s : Set F)
    (hs : ∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b')
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Finite {b : s // dI (b : F) = I} ∧
      Nat.card {b : s // dI (b : F) = I} ≤ N ^ Module.finrank ℤ (𝓞 F) * Ideal.absNorm I := by sorry
