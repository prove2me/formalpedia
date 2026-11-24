-- Prove2me | Theorems.Thm_GlobalTheory_SW_WeilLevel_sq_le_of_finsum_eq
-- name    : GlobalTheory.SW.WeilLevel.sq_le_of_finsum_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:46:01.014831+00:00
-- url     : https://prove2.me/theorems/8a35e24f-57eb-41af-91c6-839e42653641
-- title:
--   Weil Level: sq le of finsum eq
-- statement:
--   The Weil Level construction uses the sq le of finsum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/WeilActionLevelSupNormUniformInLattice.lean#L16-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/WeilActionLevelSupNormUniformInLattice.lean#L16-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilLevel
noncomputable section

theorem GlobalTheory.SW.WeilLevel.sq_le_of_finsum_eq {A : Type} [AddCommGroup A] {s t u : AddSubgroup A} (h : s ≤ t)
    (hn : s.relIndex t ≠ 0) (hu : t.relIndex u ≠ 0) (f g : A → ℂ)
    (hf : ∀ x, ∀ y ∈ t, f (x + y) = f x) (hg : ∀ x, ∀ y ∈ t, g (x + y) = g x)
    (hf' : ∀ x, f x ≠ 0 → x ∈ u) (hg' : ∀ x, g x ≠ 0 → x ∈ u)
    (he : ∑ᶠ q : A ⧸ s, f q.out * conj (f q.out) = ∑ᶠ q : A ⧸ s, g q.out * conj (g q.out))
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) (x : A) : ‖g x‖ ^ 2 ≤ (t.relIndex u : ℝ) * B ^ 2 := by sorry
