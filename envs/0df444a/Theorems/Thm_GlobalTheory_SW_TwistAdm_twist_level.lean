-- Prove2me | Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_level
-- name    : GlobalTheory.SW.TwistAdm.twist_level
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:33.878505+00:00
-- url     : https://prove2.me/theorems/a69a0c28-03c2-425f-883d-265a79f6ca1b
-- title:
--   Twist Adm: twist level
-- statement:
--   The Twist Adm construction uses the twist level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L257-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L257-L318

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

theorem GlobalTheory.SW.TwistAdm.twist_level {M R : ℕ}
    {φ : _root_.GlobalTheory.SW.Fam E n N} {𝔛 : _root_.GlobalTheory.SW.Lt E N}
    (hφ : _root_.GlobalTheory.SW.admitted M R φ)
    (hA : _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N))
    (a : Matrix (Fin N) (Fin N) E) (c : ℕ)
    (h1 : ∀ v ∈ _root_.GlobalTheory.SW.stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v)
    (h2 : ∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ _root_.GlobalTheory.SW.stdL E N)
    {Λ : _root_.GlobalTheory.SW.Lt E n} (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) :
    _root_.GlobalTheory.SW.LevelL Λ (R * c) (fun x : Matrix (Fin n) (Fin N) E =>
      _root_.GlobalTheory.SW.twist R 𝔛 φ Λ
        (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) x a)) := by sorry
