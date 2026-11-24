-- Prove2me | Theorems.Thm_GlobalTheory_SW_Dict_map_ofQ
-- name    : GlobalTheory.SW.Dict.map_ofQ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:37:14.916317+00:00
-- url     : https://prove2.me/theorems/03e350b8-24f5-4c6f-9bd5-246f1dca97e7
-- title:
--   Dict: map of Q
-- statement:
--   The Dict construction uses the map of Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L256-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHEqThSDictionary.lean#L256-L263

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
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable (Ψ : Finset (E →+* ℂ))
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable (Ψ : Finset (E →+* ℂ))

theorem GlobalTheory.SW.Dict.map_ofQ (σ : E →+* ℂ)
    (m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ) (k : Fin n) (a : Fin N) :
    σ (_root_.GlobalTheory.SW.ofQ m k a) =
      _root_.GlobalTheory.SW.Dict.vec σ (_root_.GlobalTheory.SW.qv (m k)) a := by sorry
