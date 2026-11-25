-- Prove2me | Theorems.Thm_GlobalTheory_HL_MassGlue_mass_le_and_finite
-- name    : GlobalTheory.HL.MassGlue.mass_le_and_finite
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:00:37.069957+00:00
-- url     : https://prove2.me/theorems/612443e3-88a5-431c-a0ac-043e368c0522
-- title:
--   Mass Glue: mass le and finite
-- statement:
--   The Mass Glue construction uses the mass le and finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetMassLeAndFinite.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianDoubleCosetMassLeAndFinite.lean#L105-L107

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolumeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMassEqSumFrameClassesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassesTotalWeightLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GluingImageCardPowLeDefectGroupCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianTermCountFrameClassLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetMassLeAndFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.MassGlue.mass_le_and_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → ∀ d : S.Datum, (∀ j : ℕ, (S.mass d fun Λ => S.cardI d Λ = j) ≤ ENNReal.ofReal (S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (j : ℝ) ^ (k - 1))) ∧ {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | S.IsTerm d o.out}.Finite := by sorry
