-- Prove2me | Theorems.Thm_GlobalTheory_SW_WeilAdm_eq_of_agree
-- name    : GlobalTheory.SW.WeilAdm.eq_of_agree
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:45:26.730126+00:00
-- url     : https://prove2.me/theorems/25b5b3ef-ebcd-423e-9c9b-c2b965220fbe
-- title:
--   Weil Adm: eq of agree
-- statement:
--   The Weil Adm construction uses the eq of agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleLatticeFamilyHermitianWeilAction.lean#L231-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/AdmissibleLatticeFamilyHermitianWeilAction.lean#L231-L254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_WeilActionLevelSupNormUniformInLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_AdmissibleLatticeFamilyHermitianWeilAction
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.WeilAdm
open WeilLevel Base
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ} {Λ Λ' : Lt E n}
omit [IsCMField E]

theorem GlobalTheory.SW.WeilAdm.eq_of_agree {s L : ℕ} (hs : s.Coprime L) (h2 : ∀ v ∈ Λ', (s : E) • v ∈ Λ)
    {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : LevelL Λ' L φ) (hψ : LevelL Λ' L ψ)
    (h : ∀ x, ColsIn Λ ((L : E) • x) → ColsIn Λ' ((L : E) • x) → φ x = ψ x) : φ = ψ := by sorry
