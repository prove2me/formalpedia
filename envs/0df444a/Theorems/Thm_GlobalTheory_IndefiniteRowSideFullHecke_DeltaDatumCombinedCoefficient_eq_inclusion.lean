-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DeltaDatumCombinedCoefficient_eq_inclusion
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.eq_inclusion
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:15:29.115749+00:00
-- url     : https://prove2.me/theorems/64f12aaa-0b08-4afa-92bc-e703c3e5b9bb
-- title:
--   Delta Datum Combined Coefficient: eq inclusion
-- statement:
--   The Delta Datum Combined Coefficient construction uses the eq inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/DeltaDatumCombinedCoefficient.lean#L145-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/DeltaDatumCombinedCoefficient.lean#L145-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NsmulMemSmulTop
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeltaDatumCombinedCoefficient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H}

theorem GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.eq_inclusion (a : IsAuxiliarySplitSquarefreeLevel l) (jK : KA l →+* KA a.l₂) (hj : ∀ x, ((jK x : KA a.l₂) : ℂ) = ((x : KA l) : ℂ)) :
    jK = (IntermediateField.inclusion a.KA_le).toRingHom := by sorry
