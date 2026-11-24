-- Prove2me | Theorems.Thm_GlobalTheory_SW_twist_admissible
-- name    : GlobalTheory.SW.twist_admissible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:32.99887+00:00
-- url     : https://prove2.me/theorems/d08e7184-7268-4d9e-849b-5052b73fefcb
-- title:
--   SW: twist admissible
-- statement:
--   The SW construction uses the twist admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L393-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L393-L439

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
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical

theorem GlobalTheory.SW.twist_admissible : ∀ (E : Type) [Field E]
    [NumberField E] [IsCMField E] (n N M R : ℕ) (φ : _root_.GlobalTheory.SW.Fam E n N)
    (𝔛 : _root_.GlobalTheory.SW.Lt E N), _root_.GlobalTheory.SW.admitted M R φ → 𝔛.FG →
    _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N) →
    (∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M, ∀ x (s : ℕ), s ≡ 1 [MOD R ^ 2] →
      (∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) → _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((s : E) • x)) →
      _root_.GlobalTheory.SW.twist R 𝔛 φ Λ x = φ Λ ((s : E) • x)) ∧
    (∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
      _root_.GlobalTheory.SW.twist R (_root_.GlobalTheory.SW.stdL E N) φ Λ = φ Λ) ∧
    _root_.GlobalTheory.SW.gidx (_root_.GlobalTheory.SW.stdL E N) = 1 ∧
    0 < _root_.GlobalTheory.SW.gidx 𝔛 ∧
    (∃ R', _root_.GlobalTheory.SW.admitted M R' (_root_.GlobalTheory.SW.twist R 𝔛 φ)) ∧
    ∀ (a : Matrix (Fin N) (Fin N) E) (c : ℕ), 0 < c → a.det ≠ 0 →
      (∀ v ∈ _root_.GlobalTheory.SW.stdL E N, ∃ ξ ∈ 𝔛, a *ᵥ ξ = (c : E) • v) →
      (∀ ξ ∈ 𝔛, (c : E) • (a *ᵥ ξ) ∈ _root_.GlobalTheory.SW.stdL E N) →
      ∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
        _root_.GlobalTheory.SW.LevelL Λ (R * c) (fun x => _root_.GlobalTheory.SW.twist R 𝔛 φ Λ (x * a)) := by sorry
