-- Prove2me | Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_eq
-- name    : GlobalTheory.SW.TwistAdm.twist_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:12.409112+00:00
-- url     : https://prove2.me/theorems/8cf1617c-0c01-43c6-a730-fee74d022f17
-- title:
--   Twist Adm: twist eq
-- statement:
--   The Twist Adm construction uses the twist eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L161-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L161-L173

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
omit [IsCMField E]

theorem GlobalTheory.SW.TwistAdm.twist_eq {R : ℕ} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    (φ : _root_.GlobalTheory.SW.Fam E n N)
    (hex : ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, (s : E) • v ∈ 𝔛)
    (Λ : _root_.GlobalTheory.SW.Lt E n)
    (x : Matrix (Fin n) (Fin N) E) : _root_.GlobalTheory.SW.twist R 𝔛 φ Λ x =
      if ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ then φ Λ ((hex.choose : E) • x) else 0 := by sorry
