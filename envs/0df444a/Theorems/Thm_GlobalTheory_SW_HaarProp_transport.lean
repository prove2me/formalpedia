-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarProp_transport
-- name    : GlobalTheory.SW.HaarProp.transport
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:08.70329+00:00
-- url     : https://prove2.me/theorems/50bfa130-d0c5-4956-8a69-d1201dfbe8b5
-- title:
--   Haar Prop: transport
-- statement:
--   The Haar Prop construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportional.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatRationalCoordsIntegralProportional.lean#L21-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportional
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarProp
open HaarLevel

theorem GlobalTheory.SW.HaarProp.transport {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (t : AddSubgroup B)
    (φ : B → ℂ) (hφ : ∀ x, ∀ y ∈ t, φ (x + y) = φ x) :
    ∃ g : (A ⧸ t.comap e.toAddMonoidHom) ≃ (B ⧸ t), ∀ q, φ (e q.out) = φ (g q).out := by sorry
