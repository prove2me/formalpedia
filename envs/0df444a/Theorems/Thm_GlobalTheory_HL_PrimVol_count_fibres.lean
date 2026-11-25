-- Prove2me | Theorems.Thm_GlobalTheory_HL_PrimVol_count_fibres
-- name    : GlobalTheory.HL.PrimVol.count_fibres
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:03:30.50718+00:00
-- url     : https://prove2.me/theorems/b71b3fdb-df69-4994-b293-157830e135c4
-- title:
--   Prim Vol: count fibres
-- statement:
--   The Prim Vol construction uses the count fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesHermitianGramCosetContent.lean#L17-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesHermitianGramCosetContent.lean#L17-L70

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentIndependentNonnegStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContent
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimVol

theorem GlobalTheory.HL.PrimVol.count_fibres {W W' : Type} [AddCommGroup W] [AddCommGroup W'] (T : AddSubgroup W)
    (H : AddSubgroup W') (Pr : W → Prop) (g : W → W') (B : Set W') (Q : ℝ)
    (hB : ∀ x ∈ B, ∀ a ∈ H, x + a ∈ B)
    (hfin : ((QuotientAddGroup.mk : W' → W' ⧸ H) '' B).Finite)
    (hg : ∀ z z', Pr z → Pr z' → z - z' ∈ T → g z - g z' ∈ H)
    (hfib : ∀ G ∈ B, ((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z - G ∈ H}).Finite ∧
      Q ≤ 2 * (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z - G ∈ H}).ncard : ℝ) ∧
      (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z - G ∈ H}).ncard : ℝ) ≤ 2 * Q) :
    ((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B}).Finite ∧
      (((QuotientAddGroup.mk : W' → W' ⧸ H) '' B).ncard : ℝ) * Q ≤
        2 * (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B}).ncard : ℝ) ∧
      (((QuotientAddGroup.mk : W → W ⧸ T) '' {z | Pr z ∧ g z ∈ B}).ncard : ℝ) ≤
        2 * ((((QuotientAddGroup.mk : W' → W' ⧸ H) '' B).ncard : ℝ) * Q) := by sorry
