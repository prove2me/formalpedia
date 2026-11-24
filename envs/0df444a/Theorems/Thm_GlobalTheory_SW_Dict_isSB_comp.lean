-- Prove2me | Theorems.Thm_GlobalTheory_SW_Dict_isSB_comp
-- name    : GlobalTheory.SW.Dict.isSB_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:31.840702+00:00
-- url     : https://prove2.me/theorems/12c78338-2899-4455-83aa-824ea4cea164
-- title:
--   Dict: is SB comp
-- statement:
--   The Dict construction uses the is SB comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L23-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L23-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real

theorem GlobalTheory.SW.Dict.isSB_comp {K K' κ ι κ' ι' : Type} [Field K] [Field K']
    (e : Matrix κ ι K →+ Matrix κ' ι' K') (D D' : ℕ) (hD : 0 < D) (hD' : 0 < D')
    (h1 : ∀ x, _root_.GlobalTheory.SW.IntM x → _root_.GlobalTheory.SW.IntM (D • e x))
    (h2 : ∀ x, _root_.GlobalTheory.SW.IntM (e x) → _root_.GlobalTheory.SW.IntM (D' • x))
    {φ : Matrix κ' ι' K' → ℂ} (h : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB (fun x => φ (e x)) := by sorry
