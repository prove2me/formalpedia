-- Prove2me | Theorems.Thm_GlobalTheory_SublatCount_encard_eq_of_bijOn
-- name    : GlobalTheory.SublatCount.encard_eq_of_bijOn
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:53:56.033644+00:00
-- url     : https://prove2.me/theorems/a8b719b7-8109-4152-9a12-fcae81a4b5e2
-- title:
--   Sublat Count: encard eq of bij On
-- statement:
--   The Sublat Count construction uses the encard eq of bij On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardSublatticesQuotientProdDegreeOnePrimes.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardSublatticesQuotientProdDegreeOnePrimes.lean#L18-L20

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

theorem GlobalTheory.SublatCount.encard_eq_of_bijOn {α β : Type} {s : Set α} {t : Set β} {f : α → β} (h : Set.BijOn f s t) :
    s.encard = t.encard := by sorry
