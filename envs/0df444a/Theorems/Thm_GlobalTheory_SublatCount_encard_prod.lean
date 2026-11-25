-- Prove2me | Theorems.Thm_GlobalTheory_SublatCount_encard_prod
-- name    : GlobalTheory.SublatCount.encard_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:03.378075+00:00
-- url     : https://prove2.me/theorems/6fe272ad-d3fb-42f4-bd32-fc51afbdb7cb
-- title:
--   Sublat Count: encard prod
-- statement:
--   The Sublat Count construction uses the encard prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardSublatticesQuotientProdDegreeOnePrimes.lean#L118-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardSublatticesQuotientProdDegreeOnePrimes.lean#L118-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesQuotientProdDegreeOnePrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.SublatCount
variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]

theorem GlobalTheory.SublatCount.encard_prod [IsDomain O] [Module.Finite O N] [Module.Projective O N] (T : ℕ) (hT : T ≠ 0)
    (s : Finset (Ideal O)) (hs : ∀ P ∈ s, P.IsMaximal ∧ Nat.card (O ⧸ P) = T) :
    (Ker (∏ P ∈ s, P) N).encard =
      (((∑ i ∈ Finset.range (Module.finrank O N), T ^ i) ^ s.card : ℕ) : ℕ∞) := by sorry
